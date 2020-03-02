
(* here are some example results using the definitions from increment.v *)

Require Import Increment.Increment.
Require Import Arith.


(* we'll need this for preservation *)
Lemma le_add : forall a b c, a <= b -> a <= b + c.
Proof.
  intros a b c H.
  rewrite Nat.add_comm.
  induction c as [| c' IH].
  - simpl. assumption.
  - simpl. apply le_S. assumption.
Qed.

(* statement of the main invariant we'd like to prove *)
Definition invariant s := (2 <= x s).

(* proof that each transition function preserves our invariant *)
Theorem preservation : forall (s : State) , invariant s -> invariant (incr s).
Proof.
  intros s H.
  unfold incr.
  unfold invariant in *.
  destruct (range (x s)).
  - simpl. apply le_add. assumption.
  - assumption.
Qed.

(* now we combine everything to prove that reachability implies the invariant *)
Theorem safety : forall (s : State) , reachable s -> invariant s.
Proof.
  intros s H.
  induction H as [| s' H' IH].
  - simpl. apply le_n.
  - apply preservation. apply IH.
Qed.
