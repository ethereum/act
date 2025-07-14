(** library to be included with user coq developments *)
From Stdlib Require Import ZArith.
From Stdlib Require Import Relation_Definitions.
From Stdlib Require Import Relation_Operators.

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

(** * predicates *)
Definition multistep {A : Type} (step : A -> A -> Prop) := clos_refl_trans_n1 A step.

(** * lemmas *)

Lemma step_multi_step {A} (step : A -> A -> Prop) (P : A -> A -> Prop) :
  (forall s s', step s s' -> P s s') ->
  reflexive A P ->
  transitive A P ->
  (forall s s', multistep step s s' -> P s s').
Proof.
  intros. induction H2.
  - apply H0.
  - eapply H1.
    + eassumption.
    + apply H. assumption.
Qed.

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
