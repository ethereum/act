Require Import Multi.Multi.
Require Import Coq.ZArith.ZArith.
Require Import ActLib.ActLib.


Import C.

       
Theorem reachable_value_f S0 S:
  reachable S0 S ->
  forall x, A.f (B.a (b S)) x = 0 \/ A.f (B.a (b S)) x = 2.
Proof.
  intros HR x. induction HR.
  - simpl; eauto.

  - induction H. simpl. destruct (x =? i).
    + eauto.
    + eauto.
    + eauto. 
Qed.

Theorem reachable_value_x S0 S:
  reachable S0 S ->
  w S = 0 \/ w S = 1. 
Proof.
  intros HR. induction HR; [ | induction H]; simpl; eauto. 
Qed.
