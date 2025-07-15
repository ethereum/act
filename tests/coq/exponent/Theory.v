Require Import Exponent.Exponent.
Require Import ActLib.ActLib.
Require Import Coq.ZArith.ZArith Lia.
Open Scope Z_scope.

Import Exponent.

Lemma pow_pred : forall a e, 0 < e -> a * a ^ (Z.pred e) = a ^ e.
Proof.
  intros a e Hlt.
  apply eq_sym.
  replace (a ^ e) with (a ^ (Z.succ (Z.pred e))).
  - apply Z.pow_succ_r.
    apply Zlt_0_le_0_pred.
    assumption.
  - rewrite (Z.succ_pred e).
    reflexivity.
Qed.

Lemma invariant : forall base s,
  reachableFromInit base s -> (r s) * (b s) ^ ((e s) - 1) = (b base) ^ (e base).
Proof.
  intros base s Hreach. destruct Hreach as [ Hinit Hmulti ]. induction Hmulti as [ | s s' Hstep ].
  - simpl. induction Hinit.
    rewrite Z.sub_1_r.
    apply pow_pred.
    apply Z.gt_lt.
    assumption.
  - simpl.
    rewrite <- IHHmulti.
    rewrite Z.sub_1_r.
    rewrite <- (pow_pred (b s) (e s - 1)).
    + induction Hstep.
      rewrite Z.mul_assoc. reflexivity.
    + induction Hstep. lia. 
Qed.

Theorem exp_correct : forall base s,
  reachableFromInit base s -> e s = 1 -> r s = (b base) ^ (e base).
Proof.
  intros base s H He.
  apply invariant in H.
  rewrite He in H. simpl in H.
  rewrite (Z.mul_1_r (r s)) in H.
  assumption.
Qed.
