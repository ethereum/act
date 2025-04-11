# Coq

While the automated proof backend is quite capable, there are still many properties that are too
challenging for automated tools. For this reason Act allows exporting the transition system to the
Coq proof assistant, where manual proofs of arbitrary complexity can be carried out.

A proof assistant provides tools that help to construct proofs. Coq, in particular, is highly
interactive. The user typically builds proofs step by step, with the software giving feedback as the
proof progresses.

The requirements on proofs in a system like Coq, Isabelle, or Lean are quite strict. These tools
only accept proofs that are algorithmically verifiable to be valid series of applications of the
system’s inference rules. This is generally stricter than what is typically expected of pen and
paper proofs, which often omit tedious details in the interest of clarity and concision.

The verification of these proofs is performed in a minimal and well-audited kernel. Although
occasionally bugs have been found in Coq’s and other systems’ kernels, a proof in these systems is
generally quite strong evidence of correctness.

## Usage

To generate the Coq code run
```sh
act coq --file <PATH_TO_SPEC>
```
against your spec.

To fully use this feature you should also set up a `Makefile` and `_CoqProject`, see the example in `tests/coq/ERC20/`.

If you are using Coq in your editor in an interactive mode, make sure your editor links to the Coq executables (coqtop) from the nix shell.
Alternatively you can use a local Coq executable, if present, and `make` outside of the nix shell, once the `act coq` command has terminated.

## A Brief Introduction to Proof in Coq

Coq is a complex system with a steep learning curve, and while a full tutorial on programming in Coq
is out of the scope of this blog post, we can give a little taste of how things work. For a more
thorough introduction, the books Software Foundations and Certified Programming With Dependent Types
are both excellent. Software Foundations in particular is a great introduction for users with little
experience in the fields of formal logic and proof theory.

The Coq system is composed of three languages: a minimal functional programming language (Gallina),
a tactics language for proof construction (Ltac), and a “vernacular” for interaction with the
kernel. Let’s start with the very basics: defining the natural numbers and proving something about
addition.

We start by defining the type of natural numbers. There are infinitely many natural numbers, so of
course they must be defined inductively. In fact, all type definitions are done with the Inductive
vernacular command, even if they are not in fact inductive. Coq’s Inductive is analogous to
Haskell’s data and OCaml’s type (with the added power of dependent types).

We define two constructors: `O`, representing 0, and `S`, which when applied to the natural number n
produces the representation of the number `n + 1` (S as in "successor"). To give a concrete example, 3
would be represented in this encoding as `S (S (S 0)))` i.e `1 + (1 + (1 + 0))`.

```Coq
Inductive nat : Type :=
  | O
  | S (n : nat).
```

This is an example of a unary number representation. It can often be helpful to represent numbers
this way, since the inductive nature of the definition lends itself to inductive proof techniques.

Let’s continue by defining addition over our nat type:

```Coq
Fixpoint plus (n : nat) (m : nat) : nat :=
  match n with
  | O ⇒ m
  | S n' ⇒ S (plus n' m)
  end.
```

Here we define a recursive function (a `Fixpoint`) that takes two numbers n and m and returns the
sum of these two numbers. The implementation is defined recursively with pattern matching. You might
think of this definition as “unwrapping” each application of S from the first argument until we
reach its O. Then we start wrapping the second argument in the same number of Ss.

Now we’re ready to prove something! Let’s prove that `0 + n == n`:

```Coq
Theorem plus_O_n :
  forall n : nat, plus O n = n.
Proof.
  intros n. simpl. reflexivity.
Qed.
```

We first define our theorem and give it a name (plus_O_n). Then we define the proof goal, in the
form of a dependent type. We claim that for all n, where n is an instance of our nat type, 0 + n is
equal to n. Finally, we construct a proof, in the form of a series of tactics. Tactics may implement
either backwards inference (transforming the goal) or forwards inference (transforming evidence).

The best way to understand the system is to run the software yourself, and play around with the
various tactics. In this case the goal is simple enough; once we’ve specified that the proof will be
on n, Coq is able to simplify plus O n into n, leaving us the goal n = n. This turns out to be true
by the definition of equality, and we invoke definitional equality by reflexivity.

More complicated proofs do not typically require proving basic facts about arithmetic, because Coq
ships a substantial standard library of useful definitions and theorems. The above example hopefully
serves to illustrate the formal nature of proof in these systems. In many cases it can be
surprisingly hard to convince the kernel of the correctness of a statement that seems “obviously”
true.

## Act Export

Let’s take a look at using Coq to prove properties about a specification that is too difficult for
the SMT backend. The following defines a contract that implements exponentiation via repeated
multiplication. The contract is initialized with a base (`b`) and an exponent (`e`). `exp()` can then be
repeatedly called until `e` is 1, and the result can then be read from the storage variable `r`. While
obviously artificial, this example does highlight a key shortcoming of the SMT based analysis:
exponentiation with a symbolic exponent is simply inexpressible in the smt-lib language used by all
major SMT solvers, and so any contract making use of exponentiation where the exponent is a variable
of some kind (e.g. calldata, storage) will be impossible to verify using SMT. Coq has no such
restrictions, and we can export the spec below and prove correctness there.

```act
constructor of Exponent
interface constructor(uint _b, uint _e)

iff

    _e > 0

creates

    uint b := _b
    uint e := _e
    uint r := _b
```

```act
behaviour exp of Exponent
interface exp()

iff

    e > 1

iff in range uint

    r * b
    e - 1

storage

    r => r * b
    e => e - 1
    b
```

You can export the spec into Coq by running `act coq --file Exponent.act`. This will create a file called Exponent.v which contains a model of the above Act specification in Coq:

```Coq
(* --- GENERATED BY ACT --- *)

Require Import Coq.ZArith.ZArith.
Require Import ActLib.ActLib.
Require Coq.Strings.String.

Module Str := Coq.Strings.String.
Open Scope Z_scope.

Record State : Set := state
{ b : Z
; e : Z
; r : Z
}.

Definition exp0 (STATE : State)  :=
state (b STATE) (((e STATE) - 1)) (((r STATE) * (b STATE))).

Definition Exponent0 (_b : Z) (_e : Z) :=
state (_b) (_e) (_b).

Inductive reachable  : State -> State -> Prop :=
| Exponent0_base : forall (_b : Z) (_e : Z),
     (_e > 0)
  -> ((0 <= _b) /\ (_b <= (UINT_MAX 256)))
  -> ((0 <= _e) /\ (_e <= (UINT_MAX 256)))
  -> reachable (Exponent0 _b _e) (Exponent0 _b _e)

| exp0_step : forall (BASE STATE : State),
     reachable BASE STATE
  -> ((e STATE) > 1)
  -> ((0 <= ((r STATE) * (b STATE))) /\ (((r STATE) * (b STATE)) <= (UINT_MAX 256)))
  -> ((0 <= ((e STATE) - 1)) /\ (((e STATE) - 1) <= (UINT_MAX 256)))
  -> ((0 <= (r STATE)) /\ ((r STATE) <= (UINT_MAX 256)))
  -> ((0 <= (e STATE)) /\ ((e STATE) <= (UINT_MAX 256)))
  -> ((0 <= (b STATE)) /\ ((b STATE) <= (UINT_MAX 256)))
  -> reachable BASE (exp0 STATE )
.
```

Let’s break this down a bit. We have a definition of contract storage State, which consists of three
variables `b`, `e` and `r`, all of type `Z`. `Z` is an integer type using a binary encoding from the
ZArith library bundled with Coq.

Next we have `exp0`, which defines how the state is updated by the exp behaviour, and `Exponent0` which
defines how the state variables are initialized by the constructor arguments.

Finally we have an Inductive Proposition reachable that defines the conditions under which a certain
state is reachable from another. There are two parts to this definition:

- `Exponent0_base`: states that given two integers `_b` and `_e`, the initial state is reachable
- from the initial state if `_e` and `_b` are in the range of a `uint256` and `_e` is greater than
- `0`. `exp0_step`: states that for a pair of states `BASE` and `STATE`, `exp0 STATE` (i.e. the
- result of calling `exp()` against an arbitrary contract state) is reachable from `BASE` if `STATE`
- is reachable from `BASE`, all the state variables in `STATE (e, b, r)` are within the range of a
- `uint256`, the result of the calculations `r * b` and `e - 1` are within the range of a `uint256`,
- and `e` is greater than 1.

This gives us a pair of inference rules that we can use to prove facts about the set of reachable
states defined by the specification for the Exponent contract.

The core fact that we wish to prove is that when `e` is 1, `r` is equal to `b ^ e`. This can be
expressed in Coq as:

`forall (base, s : State), reachable base s -> e s = 1 -> r s = (b base) ^ (e base)`. Expressed more
verbosely: for all states `base` and `s`, if `s` is reachable from `base`, and the value of `e` in
`s` is 1, then the result variable `r` in `s` is equal to `b` from base raised to the power of `e`
from base.

The full proof is reproduced below. While an explanation of each step is out of scope for this post
(and is anyway best made with the proof loaded into an interactive instance of the Coq prover like
proof general or CoqIde), we can give a broad strokes overview.

We must first define a helper fact `pow_pred` which simply states that given two integers `a` and
`e`, if e is greater than 0 then `a * a ^ (e - 1)` is equal to `a ^ e`. This fact is needed in the
later steps of the proof. The next step is to define a loop invariant for `exp()` (i.e. a fact that
is true before and after each loop iteration). This is the Lemma `invariant`, which states that for
every state `s` reachable from `base`, `r * b ^ (e - 1)` over `s` is equal to `b ^ e` over `base`.
Intuitively, this states that the partial result calculated so far (`r`), multiplied by the
remaining portion of the input calculation `b ^ (e - 1)` is equal to the final expected result.
Finally, given these two intermediate facts, we can discharge a proof for the correctness of
Exponent as defined above.

```Coq
Require Import Exponent.Exponent.
Require Import ActLib.ActLib.
Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Lemma pow_pred : forall a e, 0 < e -> a * a ^ (Z.pred e) = a ^ e.
Proof.
  intros.
  apply eq_sym.
  replace (a ^ e) with (a ^ (Z.succ (Z.pred e))).
  - apply Z.pow_succ_r.
    apply Zlt_0_le_0_pred.
    assumption.
  - rewrite (Z.succ_pred e).
    reflexivity.
Qed.

Lemma invariant : forall base s,
  reachable base s -> (r s) * (b s) ^ ((e s) - 1) = (b base) ^ (e base).
Proof.
  intros base s H. induction H.
  - simpl.
    rewrite Z.sub_1_r.
    apply pow_pred.
    apply Z.gt_lt.
    assumption.
  - simpl.
    rewrite <- IHreachable.
    rewrite Z.sub_1_r.
    rewrite <- (pow_pred (b STATE) (e STATE - 1)).
    + rewrite Z.mul_assoc. reflexivity.
    + apply Z.gt_lt in H0.
      apply (proj1 (Z.sub_lt_mono_r 1 (e STATE) 1)).
      assumption.
Qed.

Theorem exp_correct : forall base s,
  reachable base s -> e s = 1 -> r s = (b base) ^ (e base).
Proof.
  intros base s H He.
  apply invariant in H.
  rewrite He in H. simpl in H.
  rewrite (Z.mul_1_r (r s)) in H.
  assumption.
Qed. Check exp_correct.
```

While this may seem like quite a lot of work to prove what looks like a pretty simple and obvious fact it is worth noting two things:

- A proof of this property is beyond the reach of any automated tool available today.
- Our mind is full of hidden assumptions, and facts that may seem obvious are not always so. This is not the case for the Coq proof kernel, and once we have convinced it that something is true, we can be very sure that it really is.
