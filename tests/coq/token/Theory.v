Require Import Coq.ZArith.ZArith.
Require Import ActLib.ActLib.
Require Coq.Strings.String.
Require Import Lia.


Require Import Token.Token. 

(* Address should be Z or N? Or int20? Or { n : N | } *) 

Definition MAX_ADDRESS := UINT_MAX 160.


Fixpoint balances_sum' (balances : address -> Z) (n : nat) (acc : Z) : Z :=
    match n with
    | O => balances 0 + acc
    | S n => balances_sum' balances n (acc + balances (Z.of_nat (S n))) 
    end.

Definition balances_sum (STATE : State) :=
  balances_sum' (balances STATE) (Z.to_nat MAX_ADDRESS) 0. 


Definition transfer_from map (from : address) (amt : Z) :=
  fun b => if b =? from then map from - amt else map b.

Definition transfer_to map (from : address) (amt : Z) :=
  fun b => if b =? from then map from + amt else map b.

Definition transfer map from to amt := transfer_to (transfer_from map from amt) to amt.

Lemma balances_sum_f_eq f f' addr acc :
  (forall x, x <= Z.of_nat addr -> f x = f' x) ->
  balances_sum' f addr acc = balances_sum' f' addr acc. 
Proof.
  revert acc. induction addr; intros acc Hyp. 
  - simpl. rewrite Hyp. reflexivity. lia.
  - simpl. rewrite IHaddr. rewrite Hyp. reflexivity.
    lia. intros. eapply Hyp. lia.
Qed.     

Lemma balances_sum_acc f  addr acc z :
  balances_sum' f addr (acc + z) = balances_sum' f addr acc + z. 
Proof.
  revert z acc. induction addr; intros z acc. 
  - simpl. lia.
  - simpl. rewrite !IHaddr. lia.
Qed.

Opaque Z.sub Z.add Z.of_nat.


Lemma balances_sum_thm x f f' addr acc :
  (forall y, x <> y -> f y = f' y) ->
  0 <= x ->
  balances_sum' f addr acc =
  if (Z.to_nat x <=? addr)%nat then balances_sum' f' addr acc - f' x + f x else balances_sum' f' addr acc. 
Proof.
  revert acc. induction addr; intros acc Hyp Hleq1.
  - simpl. destruct (0 =? x) eqn:Heq. 
    + eapply Z.eqb_eq in Heq. subst.
      simpl. lia.
    + eapply Z.eqb_neq in Heq.
      assert (Hbeq : (Z.to_nat x <=? 0)%nat = false).
      { eapply leb_correct_conv. simpl. lia. }
      rewrite Hbeq. rewrite Hyp. reflexivity. eauto. 

  - destruct (Z.to_nat x <=? S addr)%nat eqn:Hleq.
    + eapply Nat.leb_le in Hleq. 
      destruct (Z.of_nat (S addr) =? x) eqn:Heqb.
      * eapply Z.eqb_eq in Heqb. simpl. rewrite Heqb.
        erewrite balances_sum_f_eq with (f' := f').  
        rewrite !balances_sum_acc. lia.

        intros. eapply Hyp. lia.

      * simpl. 
        destruct ((Z.to_nat x <=? addr)%nat) eqn:Hleq'.
        -- rewrite IHaddr; eauto. rewrite Hyp. reflexivity.
           intros Heq; subst. lia. 
        -- eapply Z.eqb_neq in Heqb.
           eapply Nat.leb_gt in Hleq'. lia.

    + simpl. eapply leb_complete_conv in Hleq.
      erewrite balances_sum_f_eq with (f' := f').
      rewrite Hyp. reflexivity.
      * intros Heq; subst. lia.
      * intros. rewrite Hyp. reflexivity.
        intros Heq; subst. lia.
Qed.


Lemma balances_sum_transfer_from map from amt addr acc :
  0 <= from ->
  balances_sum' (transfer_from map from amt) addr acc =
  if (Z.to_nat from <=? addr)%nat then balances_sum' map addr acc - amt else balances_sum' map addr acc. 
Proof.
  intros Hleq1.
  erewrite balances_sum_thm with (f := transfer_from map from amt) (f' := map) (x := from); eauto.

  - destruct (Z.to_nat from <=? addr)%nat eqn:Hleq.

    unfold transfer_from. rewrite Z.eqb_refl. lia.

    reflexivity.

  - intros. unfold transfer_from. eapply Z.eqb_neq in H.
    rewrite Z.eqb_sym, H. reflexivity.
Qed.

Lemma balances_sum_transfer_to map to amt addr acc :
  0 <= to ->
  balances_sum' (transfer_to map to amt) addr acc =
  if (Z.to_nat to <=? addr)%nat then balances_sum' map addr acc + amt else balances_sum' map addr acc. 
Proof.
  intros Hleq1.
  erewrite balances_sum_thm with (f := transfer_to map to amt) (f' := map) (x := to); eauto.

  - destruct (Z.to_nat to <=? addr)%nat eqn:Hleq.

    unfold transfer_to. rewrite Z.eqb_refl. lia.

    reflexivity.

  - intros. unfold transfer_to. eapply Z.eqb_neq in H.
    rewrite Z.eqb_sym, H. reflexivity.
Qed.


Theorem transfer_thm map from to amt addr acc: 
  to <> from ->
  0 <= from <= Z.of_nat addr ->
  0 <= to <= Z.of_nat addr ->
  balances_sum' (transfer map from to amt) addr acc  = balances_sum' map addr acc. 
Proof.
  intros Hneq Hleq1 Hleq2.
  unfold transfer. 
  
  rewrite balances_sum_transfer_to; [ | lia ].
  rewrite leb_correct; [ | lia ].
  
  rewrite balances_sum_transfer_from; [ | lia ].
  rewrite leb_correct; [ | lia ].

  lia.
Qed. 
      
    
Theorem constant_balances : forall BASE STATE, 
    reachable BASE STATE ->
    balances_sum BASE = balances_sum STATE.
Proof.
  intros BASE S Hreach. induction Hreach; intros.
  - reflexivity.
  - rewrite IHHreach. unfold transfer0. 
    unfold balances_sum. simpl.
    
    erewrite <- transfer_thm.
    
    + unfold transfer, transfer_to, transfer_from.
      eapply not_eq_sym in H. eapply Z.eqb_neq in H.
      rewrite H. reflexivity.

    + eauto.
    + rewrite Z2Nat.id. assumption.
      unfold MAX_ADDRESS. unfold UINT_MAX. lia.

    + rewrite Z2Nat.id. assumption.
      unfold MAX_ADDRESS. unfold UINT_MAX. lia.

  - unfold transfer1. rewrite IHHreach.
    reflexivity.
Qed. 
