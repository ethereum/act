(** library to be included with user coq developments *)

Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

(** addresses are interpreted as integers *)
Definition address := Z.

(** integer bounds *)
Definition UINT_MIN (n : Z) := 0.
Definition UINT_MAX (n : Z) := 2^n - 1.
Definition INT_MIN  (n : Z) := 0 - 2^(n - 1).
Definition INT_MAX  (n : Z) := 2^(n - 1) - 1.

(** notations *)
Notation "a =?? b" := (bool_eq a b) (at level 70, no associativity).
