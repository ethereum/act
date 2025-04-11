(** library to be included with user coq developments *)
From Stdlib Require Import ZArith.

Print LoadPath.
(** * type definitions *)
Definition address := Z.

(** * Environment record *)
Record Env : Set :=
  { Callvalue : Z;
    Caller : address;
    Blockhash : Z;
    Blocknumber : Z;
    Difficulty : Z;
    Timestamp : Z;
    Gaslimit : Z;
    Coinbase : address;
    Chainid : Z;
    This : address;
    Origin : address;
    Nonce : Z;
    Calldepth : Z }.

(** * integer bounds *)
Definition UINT_MIN (n : Z) := 0.
Definition UINT_MAX (n : Z) := (2^n - 1)%Z.
Definition INT_MIN  (n : Z) := (0 - 2^(n - 1))%Z.
Definition INT_MAX  (n : Z) := (2^(n - 1) - 1)%Z.

(** * notations *)
Notation "a =?? b" := (bool_eq a b) (at level 70, no associativity).
Definition range256 (n : Z) := (0 <= n <= UINT_MAX 256)%Z.

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
