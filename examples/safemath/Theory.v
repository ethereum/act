Require Import SafeMath.SafeMath.
Require Import ActLib.ActLib.
Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

(* trivial observation that there is only one possible state *)
Lemma state_constant : forall s, s = state.
Proof.
  intros.
  destruct s.
  reflexivity.
Qed.

Theorem mul_correct : forall s x y,
  range256 x /\ range256 y /\ range256 (x * y) <-> mul0_ret s x y (x * y).
Proof.
  intros.
  split. {
    intros.
    destruct H as [Hx [Hy Hxy]].
    apply mul0_ret_intro.
    - assumption.
    - assumption.
    - assumption.
  } {
    intros. induction H.
    split. assumption.
    split. assumption. assumption.
  }
Qed. Check mul_correct.

