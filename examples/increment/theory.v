
(* here are some example results using the definitions from increment.v *)

Require Import Increment.increment.
Require Import PeanoNat.
Require Import Plus.


(* some arithmetic lemmas we'll need. i'm sure there are nicer ways of doing
   this.
 *)

Lemma pluszero : forall (n : nat) , n + 0 = n.
Proof.
  intros n.
  rewrite plus_comm. reflexivity.
Qed.

Lemma plusone : forall (n : nat) , n + 1 = S n.
Proof.
  intros n.
  rewrite plus_comm. reflexivity.
Qed.    


(* statement of the main invariant we'd like to prove *)
Notation invariant s := (2 <= x s).

(* proof that each transition function preserves our invariant *)
Theorem preservation : forall (s : State) , invariant s -> invariant (incr s).
Proof.
  intros s H.
  unfold incr.
  destruct (range (x s)).
  - simpl. rewrite -> plusone.
    apply le_S. apply H.
  - apply H.
Qed.

(* now we combine everything to prove that reachability implies the invariant *)
Theorem safety : forall (s : State) , reachable s -> invariant s.
Proof.
  intros s H.
  induction H as [| s' H' IH].
  - simpl. apply le_n.
  - apply preservation. apply IH.
Qed.
