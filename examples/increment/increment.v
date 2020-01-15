
(* goal is to generate something like this file from the act spec *)

Require Import PeanoNat.

(* some boilerplate *)
Definition UINT_MIN := 0.
Definition UINT_MAX := 2 ^ 8. (* fix later *)
Definition range (n : nat) := andb (UINT_MIN <=? n) (n <=? UINT_MAX).
Definition range' (n : nat) := (n >= UINT_MIN) /\ (n <= UINT_MAX).

(* type of contract states *)
Record State : Set := state
{
  x : nat
}.

(* initial state *)
Definition BASE := state 2.

(* here we postulate the existence of the various contract functions
   described in the spec. these functions are described by collections of
   propositions rather than by constructive definitions, because we may not
   be given total specifications for them.
 *)
Axiom incr' : State -> State.
Axiom incr'_p0 :
  forall (s : State) ,   range' (x s + 1) -> incr' s = state (x s + 1).
Axiom incr'_p1 :
  forall (s : State) , ~ range' (x s + 1) -> incr' s = s.
Axiom incr'_p2 :
  forall (s : State) , incr' s = state (x s + 1) \/ incr' s = s.

(* alternatively, we could assume a total spec is given and generate
   a gallina definition
 *)
Definition incr (s : State) :=
  match range (x s) with
  | true => state (x s + 1)
  | false => s
  end.

(* definition of exactly which states are reachable *)
Inductive reachable : State -> Prop :=
| base : reachable BASE
| incr_step : forall (s : State) , reachable s -> reachable (incr s)
.
