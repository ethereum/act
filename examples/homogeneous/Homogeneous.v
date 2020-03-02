Require Import ZArith.
Open Scope Z_scope.

Definition UINT_MIN := 0.
Definition UINT_MAX := 2 ^ 256.
Definition range (n : Z) := ((UINT_MIN <=? n) && (n <? UINT_MAX)) % bool.

Record State : Set :=
  state {
      x : Z ;
      y : Z ;
      z : Z ;
    }.

Definition BASE := state 3 5 15.

Definition f (s : State) (scalar : Z) :=
  let x := x s in
  let y := y s in
  let z := z s in
  match range (x * scalar) , range (z * scalar) with
  | true , true => {| x := x * scalar ; y := y ; z := z * scalar |}
  | _ , _ => s
  end.

Definition g (s : State) (scalar : Z) :=
  let x := x s in
  let y := y s in
  let z := z s in
  match range (y * scalar) , range (z * scalar) with
  | true , true => {| x := x ; y := y * scalar ; z := z * scalar |}
  | _ , _ => s
  end.

Inductive reachable : State -> Prop :=
| base : reachable BASE
| f_step : forall (s : State) (scalar : Z), reachable s -> reachable (f s scalar)
| g_step : forall (s : State) (scalar : Z), reachable s -> reachable (g s scalar)
.
