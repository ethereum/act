# Introduction

Act is a high level specification language for EVM programs. The core aim is to allow for easy
refinement. We want to make it as easy as possible for development teams to define a high level
specification, which can then be used "upwards" to prove higher level properties or
"downwards" to demonstrate that an implementation in EVM bytecode conforms to the spec.

Act currently integrates with the following tools:

- Hevm: automated refinement proof between the act spec and a given evm bytecode object
- SMT: automated proof of invariants and postconditions
- Coq: manual proof of high level properties against a model derived from the Act spec

## Overview

At a very high level Act is a kind of mathy english over the EVM, where contracts are defined as a
set of pure functions taking a given EVM state (i.e. storage & blockchain context) and some calldata
and producing a new EVM state (`(EVM, Calldata) -> EVM`).

A specification of a contract written in Act consists of a constructor and a set of behaviours:

The constructor specification defines the structure of the contract’s state, the initial value of
the state, and a list of invariants that the contract should satisfy.

Each behaviour specification determines how a contract method updates the state, the method’s return
value (if any), and any conditions that must be satisfied in order for the state update to be
applied.

Alternatively, they can be thought of as an initial state and a set of state transitions,
determining an inductively defined state transition system.

## Types

The types of Act consist of three basic primitives: Integers, Booleans and Bytestrings. Integers are
unbounded, with true integer operations. However, as our integer expressions will often represent
words in the EVM, we allow ourselves a slight abuse of notation and denote by uintN/intN integers
together with the constraint that the value fits into a uintN/intN. If any operation could over- or
underflow this bound, the constraint will be unfulfilled and the specification will fail to prove.

Using conventional ABI types for typing also allows us to specify function signatures in a concise
way. As an example, consider this specification of a trivial contract that adds two numbers and
stores the result on chain:

```
constructor of Add
interface constructor()

creates

  uint result := 0

behaviour add of Add
interface add(uint x, uint y)

iff in range uint

   x + y

storage

  result => x + y

returns x + y
```

Expressed in English and math, this specification would read:

The contract `Add` has a single state variable, named `result`, which is an integer such that `0 <= result < 2^256`.

Given any pair of integers `x` and `y`, s.t. `0 <= x < 2^256` and `0 <= y < 2^256`, an ABI encoded call to the contract `Add` with the signature `add(uint256,uint256)`, with its respective arguments named `x` and `y`, will:

- store `x + y` in `result` and return `x + y` if `0 <= x + y < 2^256`
- revert otherwise

