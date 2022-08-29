Require Import Coq.ZArith.ZArith.
Require Import ActLib.ActLib.
Require Coq.Strings.String.
Require Import Lia.


Require Import ERC20.ERC20.

(* Address should be Z or N? Or int20? *)

Definition MAX_ADDRESS := UINT_MAX 160.


Fixpoint balanceOf_sum' (balanceOf : address -> Z) (n : nat) (acc : Z) : Z :=
    match n with
    | O => balanceOf 0 + acc
    | S n => balanceOf_sum' balanceOf n (acc + balanceOf (Z.of_nat (S n)))
    end.

Definition balanceOf_sum (STATE : State) :=
  balanceOf_sum' (balanceOf STATE) (Z.to_nat MAX_ADDRESS) 0.


Definition transfer_from map (from : address) (amt : Z) :=
  fun b => if b =? from then map from - amt else map b.

Definition transfer_to map (from : address) (amt : Z) :=
  fun b => if b =? from then map from + amt else map b.

Definition transfer map from to amt := transfer_to (transfer_from map from amt) to amt.

Lemma balanceOf_sum_f_eq f f' addr acc :
  (forall x, x <= Z.of_nat addr -> f x = f' x) ->
  balanceOf_sum' f addr acc = balanceOf_sum' f' addr acc.
Proof.
  revert acc. induction addr; intros acc Hyp.
  - simpl. rewrite Hyp. reflexivity. lia.
  - simpl. rewrite IHaddr. rewrite Hyp. reflexivity.
    lia. intros. eapply Hyp. lia.
Qed.

Lemma balanceOf_sum_acc f  addr acc z :
  balanceOf_sum' f addr (acc + z) = balanceOf_sum' f addr acc + z.
Proof.
  revert z acc. induction addr; intros z acc.
  - simpl. lia.
  - simpl. rewrite !IHaddr. lia.
Qed.

Opaque Z.sub Z.add Z.of_nat.


Lemma balanceOf_sum_thm x f f' addr acc :
  (forall y, x <> y -> f y = f' y) ->
  0 <= x ->
  balanceOf_sum' f addr acc =
  if (Z.to_nat x <=? addr)%nat then balanceOf_sum' f' addr acc - f' x + f x else balanceOf_sum' f' addr acc.
Proof.
  revert acc. induction addr; intros acc Hyp Hleq1.
  - simpl. destruct (0 =? x) eqn:Heq.
    + eapply Z.eqb_eq in Heq. subst.
      simpl. lia.
    + eapply Z.eqb_neq in Heq.
      assert (Hbeq : (Z.to_nat x <=? 0)%nat = false).
      { eapply leb_correct_conv. lia. }
      rewrite Hbeq. rewrite Hyp. reflexivity. eauto.

  - destruct (Z.to_nat x <=? S addr)%nat eqn:Hleq.
    + eapply Nat.leb_le in Hleq.
      destruct (Z.of_nat (S addr) =? x) eqn:Heqb.
      * eapply Z.eqb_eq in Heqb. simpl. rewrite Heqb.
        erewrite balanceOf_sum_f_eq with (f' := f').
        rewrite !balanceOf_sum_acc. lia.

        intros. eapply Hyp. lia.

      * simpl.
        destruct ((Z.to_nat x <=? addr)%nat) eqn:Hleq'.
        -- rewrite IHaddr; eauto. rewrite Hyp. reflexivity.
           intros Heq; subst. lia.
        -- eapply Z.eqb_neq in Heqb.
           eapply Nat.leb_gt in Hleq'. lia.

    + simpl. eapply leb_complete_conv in Hleq.
      erewrite balanceOf_sum_f_eq with (f' := f').
      rewrite Hyp. reflexivity.
      * intros Heq; subst. lia.
      * intros. rewrite Hyp. reflexivity.
        intros Heq; subst. lia.
Qed.


Lemma balanceOf_sum_transfer_from map from amt addr acc :
  0 <= from ->
  balanceOf_sum' (transfer_from map from amt) addr acc =
  if (Z.to_nat from <=? addr)%nat then balanceOf_sum' map addr acc - amt else balanceOf_sum' map addr acc.
Proof.
  intros Hleq1.
  erewrite balanceOf_sum_thm with (f := transfer_from map from amt) (f' := map) (x := from); eauto.

  - destruct (Z.to_nat from <=? addr)%nat eqn:Hleq.

    unfold transfer_from. rewrite Z.eqb_refl. lia.

    reflexivity.

  - intros. unfold transfer_from. eapply Z.eqb_neq in H.
    rewrite Z.eqb_sym, H. reflexivity.
Qed.

Lemma balanceOf_sum_transfer_to map to amt addr acc :
  0 <= to ->
  balanceOf_sum' (transfer_to map to amt) addr acc =
  if (Z.to_nat to <=? addr)%nat then balanceOf_sum' map addr acc + amt else balanceOf_sum' map addr acc.
Proof.
  intros Hleq1.
  erewrite balanceOf_sum_thm with (f := transfer_to map to amt) (f' := map) (x := to); eauto.

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
  balanceOf_sum' (transfer map from to amt) addr acc  = balanceOf_sum' map addr acc.
Proof.
  intros Hneq Hleq1 Hleq2.
  unfold transfer.

  rewrite balanceOf_sum_transfer_to; [ | lia ].
  rewrite leb_correct; [ | lia ].

  rewrite balanceOf_sum_transfer_from; [ | lia ].
  rewrite leb_correct; [ | lia ].

  lia.
Qed.

Ltac destructAnds :=
  repeat match goal with
    [ H : _ /\ _ |- _ ] => destruct H
  end.
 
Ltac convert_neq :=
  repeat match goal with
    [ H : _ <> _ |- _ ] => eapply not_eq_sym in H; eapply Z.eqb_neq in H
  end.

Ltac rewrite_eqs :=
  repeat match goal with
    [ H : _ =? _ = _ |- _ ] => rewrite H
  end.

Lemma balances_after_transfer ENV STATE src dst amount :
  0 <= src <= MAX_ADDRESS ->
  0 <= dst <= MAX_ADDRESS ->                       
  src <> dst ->
  balanceOf_sum STATE =
  balanceOf_sum (transferFrom0 ENV STATE src dst amount).
Proof.
  intros. unfold balanceOf_sum; simpl. 
  erewrite <- transfer_thm.

  + unfold transfer, transfer_to, transfer_from.
    convert_neq. rewrite_eqs. reflexivity.

  + eauto.

  + rewrite Z2Nat.id. assumption. 
    unfold MAX_ADDRESS. unfold UINT_MAX. lia.

  + rewrite Z2Nat.id. assumption.
    unfold MAX_ADDRESS. unfold UINT_MAX. lia.
Qed.

Theorem constant_balanceOf : forall BASE STATE,
    reachable BASE STATE ->
    balanceOf_sum BASE = balanceOf_sum STATE.
Proof.
  intros BASE S Hreach.
  induction Hreach; intros; [ reflexivity | | assumption | | | | assumption ];
    rewrite IHHreach; destructAnds.
  - eapply (balances_after_transfer ENV); eauto.
  - eapply (balances_after_transfer ENV); eauto.
  - eapply (balances_after_transfer ENV); eauto.
  - assert (Hthm := balances_after_transfer ENV STATE).
    unfold balanceOf_sum, transferFrom0, transferFrom2 in *.
    eapply Hthm; eauto.
Qed.
