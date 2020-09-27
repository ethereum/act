(** library to be included with user coq developments *)

Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

(** * type definitions *)
Definition address := Z.

(** * integer bounds *)
Definition UINT_MIN (n : Z) := 0.
Definition UINT_MAX (n : Z) := 2^n - 1.
Definition INT_MIN  (n : Z) := 0 - 2^(n - 1).
Definition INT_MAX  (n : Z) := 2^(n - 1) - 1.

(** * notations *)
Notation "a =?? b" := (bool_eq a b) (at level 70, no associativity).
Definition range256 (n : Z) := 0 <= n <= UINT_MAX 256.

(** * lemmas *)

Lemma ite_true {A : Type} : forall (b : bool) (x y : A),
  ((if b then x else y) = x) -> (x <> y) -> (b = true).
Proof.
  intros b x y H Hneq.
  induction b.
  - reflexivity.
  - apply eq_sym in H.
    destruct (Hneq H).
Qed.

Lemma ite_false {A : Type} : forall (b : bool) (x y : A),
  ((if b then x else y) = y) -> (x <> y) -> (b = false).
Proof.
  intros b x y H Hneq.
  induction b.
  - unfold not in Hneq. destruct (Hneq H).
  - reflexivity.
Qed.


