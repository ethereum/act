Require Import Homogeneous.Homogeneous.
Require Import NArith.
Open Scope N_scope.

Lemma scaling : forall (a b c : N), a = b -> a * c = b * c.
Proof.
  intros a b c H.
  rewrite H.
  reflexivity.
Qed.

Definition invariant s :=
  let x := x s in
  let y := y s in
  let z := z s in
  x * y = z.
Hint Unfold invariant.

Theorem f_preservation :
  forall (s : State) (scalar : N), invariant s -> invariant (f s scalar).
Proof.
  intros s scalar H.
  unfold invariant in *.
  unfold f.
  destruct (range (x s * scalar)).
  - destruct (range (z s * scalar)).
    + simpl.
      rewrite <- N.mul_assoc.
      rewrite (N.mul_comm scalar).
      rewrite -> N.mul_assoc.
      apply scaling with (c := scalar).
      assumption.
    + assumption.
  - assumption.
Qed.

Theorem g_preservation :
  forall (s : State) (scalar : N), invariant s -> invariant (g s scalar).
Proof.
  intros s scalar H.
  unfold invariant in *.
  unfold g.
  destruct (range (y s * scalar)).
  - destruct (range (z s * scalar)).
    + simpl.
      rewrite -> N.mul_assoc.
      apply scaling with (c := scalar).
      assumption.
    + assumption.
  - assumption.
Qed.

Theorem safety : forall (s : State) , reachable s -> invariant s.
Proof.
  intros s H.
  induction H as [| s' scalar H' IH | s' scalar H' IH].
  - unfold invariant. reflexivity.
  - apply f_preservation. apply IH.
  - apply g_preservation. apply IH.
Qed.
