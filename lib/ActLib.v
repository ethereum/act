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
Definition MOD (n : Z) := UINT_MAX n + 1.

(** * notations *)
Notation "a =?? b" := (bool_eq a b) (at level 70, no associativity).
Definition range256 (n : Z) := 0 <= n <= UINT_MAX 256.

(** * lemmas *)

Lemma ite_true {A : Type} : forall (b : bool) (x y z : A),
  ((if b then x else y) = z) -> (z <> y) -> (b = true).
Proof.
  intros b x y H Heq.
  induction b.
  - reflexivity.
  - intros Hneq.
    rewrite Heq in Hneq.
    apply except.
    apply Hneq.
    reflexivity.
Qed.

Lemma ite_false {A : Type} : forall (b : bool) (x y z : A),
  ((if b then x else y) = z) -> (z <> x) -> (b = false).
Proof.
  intros b x y H Heq.
  induction b.
  - intros Hneq.
    rewrite Heq in Hneq.
    apply except.
    apply Hneq.
    reflexivity.
  - reflexivity.
Qed.

Lemma ite_dec {A : Type} : forall (b : bool) (x y : A),
  let ite := if b then x else y in
  ite = x \/ ite = y.
Proof.
  intros. unfold ite.
  destruct b.
  - left. reflexivity.
  - right. reflexivity.
Qed.

Lemma range_mod : forall a, range256 a -> a mod (MOD 256) = a.
Proof.
  intros.
  apply Z.mod_small.
  destruct H.
  split.
  + assumption.
  + apply (Zle_lt_succ a (UINT_MAX 256)). assumption.
Qed.

