(* depends on StateMachine.v *)

Require Import StateMachine.StateMachine.
Require Import ActLib.ActLib.
Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Import StateMachine.

Theorem invariant : forall BASE s, reachable BASE s -> (x s) >= 0 /\ (x s) <= 2.
Proof.
  intros. induction H; simpl; split; easy.
Qed.

