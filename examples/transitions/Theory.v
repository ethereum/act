(* depends on StateMachine.v *)

Require Import StateMachine.StateMachine.
Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Theorem invariant : forall s, reachable s -> (x s) >= 0 /\ (x s) <= 2.
Proof.
  intros. induction H. {
    simpl. split.
    - intros contra. discriminate.
    - intros contra. discriminate.
  } {
    destruct IHreachable.
    unfold h.
    destruct ((andb ((x s) =? 2) (andb (andb (0 <=? (x s)) ((x s) <=? (UINT_MAX 256))) true))).
    simpl.
    - split. discriminate. discriminate.
    - split. assumption. assumption.
  } {
    destruct IHreachable.
    unfold g.
    destruct ((andb ((x s) =? 1) (andb (andb (0 <=? (x s)) ((x s) <=? (UINT_MAX 256))) true))).
    simpl.
    - split. discriminate. discriminate.
    - split. assumption. assumption.
  } {
    destruct IHreachable.
    unfold f.
    destruct ((andb ((x s) =? 0) (andb (andb (0 <=? (x s)) ((x s) <=? (UINT_MAX 256))) true))).
    simpl.
    - split. discriminate. discriminate.
    - split. assumption. assumption.
  }
Qed.

