(* depends on StateMachine.v *)

Require Import StateMachine.StateMachine.
Require Import ActLib.ActLib.
Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Import StateMachine.

Theorem invariant : forall s, reachable s -> (x s) >= 0 /\ (x s) <= 2.
Proof.
  intros. destruct H as [s0 Hreach].
  destruct Hreach as [ Hinit Hmulti ].
  induction Hmulti as [ | s s' Hstep]; [induction Hinit | induction Hstep]. {
    simpl. split.
    - intros contra. discriminate.
    - intros contra. discriminate.
  } {
    simpl. split.
    - intros contra. discriminate.
    - intros contra. discriminate.
  } {
    simpl. split.
    - intros contra. discriminate.
    - intros contra. discriminate.
  } {
    simpl. split.
    - intros contra. discriminate.
    - intros contra. discriminate.
  }
Qed. Check invariant.

