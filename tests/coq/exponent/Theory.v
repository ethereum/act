Require Import Exponent.Exponent.
Require Import ActLib.ActLib.
Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Lemma pow_pred : forall a e, 0 < e -> a * a ^ (Z.pred e) = a ^ e.
Proof.
  intros.
  apply eq_sym.
  replace (a ^ e) with (a ^ (Z.succ (Z.pred e))).
  - apply Z.pow_succ_r.
    apply Zlt_0_le_0_pred.
    assumption.
  - rewrite (Z.succ_pred e).
    reflexivity.
Qed.

Lemma invariant : forall base s,
  reachable base s -> (r s) * (b s) ^ ((e s) - 1) = (b base) ^ (e base).
Proof.
  intros base s H. induction H.
  - simpl.
    rewrite Z.sub_1_r.
    apply pow_pred.
    apply Z.gt_lt.
    assumption.
  - simpl.
    rewrite <- IHreachable.
    rewrite Z.sub_1_r.
    rewrite <- (pow_pred (b STATE) (e STATE - 1)).
    + rewrite Z.mul_assoc. reflexivity.
    + apply Z.gt_lt in H0.
      apply (proj1 (Z.sub_lt_mono_r 1 (e STATE) 1)).
      assumption.
Qed.

Theorem exp_correct : forall base s,
  reachable base s -> e s = 1 -> r s = (b base) ^ (e base).
Proof.
  intros base s H He.
  apply invariant in H.
  rewrite He in H. simpl in H.
  rewrite (Z.mul_1_r (r s)) in H.
  assumption.
Qed. Check exp_correct.
