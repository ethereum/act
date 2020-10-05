Require Import Exponent.Exponent.
Require Import ActLib.ActLib.
Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Lemma invariant : forall base s,
  reachable base s -> (r s) * (b s) ^ ((e s) - 1) = (b base) ^ (e base).
Proof.
  intros base s H. induction H.
  - simpl. omega.
  - simpl.
    rewrite <- IHreachable.
    omega.
Qed.

Theorem exp_correct : forall base s,
  reachable base s -> e s = 1 -> r s = (b base) ^ (e base).
Proof.
  intros base s H He.
  apply invariant in H.
  rewrite He in H. simpl in H.
  rewrite (Z.mul_1_r (r s)) in H.
  assumption.
Qed.
