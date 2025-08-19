Require Import SafeMath.SafeMath.
Require Import ActLib.ActLib.
Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Import SafeMath.

(* trivial observation that there is only one possible state *)
Lemma state_constant : forall s, s = state.
Proof.
  intros.
  destruct s.
  reflexivity.
Qed.

Theorem mul_correct : forall e s x y,
  range256 x /\ range256 y /\ range256 (x * y) <-> mul0_ret e s x y (x * y).
Proof.
  intros.
  split. {
    intros.
    destruct H as [Hx [Hy Hxy]].
    apply mul0_ret_intro.
    - split; [ assumption | ].
      split; assumption.
    - assumption.
    - assumption.
    - assumption.
    - assumption.
    - eauto.
  } {
    intros. destruct H.
    split. assumption.
    split. assumption.
    easy.
  }
Qed.


Theorem mul_is_mul :
  forall e s x y z,
    mul0_ret e s x y z ->
    z = x * y.
Proof.
  intros. inversion H.
  reflexivity.
Qed.
