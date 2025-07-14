Require Import Multi.Multi.
Require Import Coq.ZArith.ZArith.
Require Import ActLib.ActLib.


Import C.


Theorem reachable_value_f S:
  reachable S ->
  forall x, A.f (B.a (b S)) x = 0 \/ A.f (B.a (b S)) x = 2.
Proof.
  intros HR x. destruct HR as [ S0 Hreach], Hreach as [ Hinit Hmulti ].
  induction Hmulti as [ | S' S'' Hstep ].
  - induction Hinit. simpl; eauto.

  -  induction Hstep. simpl. destruct (x =? i).
    + eauto.
    + eauto.
    + eauto.
Qed.

Theorem reachable_value_x S:
  reachable S ->
  w S = 0 \/ w S = 1.
Proof.
  intros HR. destruct HR as [ S0 Hreach], Hreach as [ Hinit Hmulti ].
  induction Hmulti as [ | S' S'' Hstep ]; [induction Hinit | induction Hstep ]; simpl; auto.
Qed.
