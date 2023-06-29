# Syntax of the Act language

A specification of a contract written in `act` consists of a
`constructor` and a set of `behaviours`.

The `constructor` specification defines the structure of the contract
state, the initial value for the state, and a list of invariants that
the contract should satisfy.

Each `behaviour` specification determines how a contract method updates
the state, and its return value, and the conditions that must be
satisfied in order for it to be applied.

Alternatively, they can be thought of an initial state and a
set of state transitions, determining an inductively defined
state transition system.

The specifications can be exported to different backends in order to
prove that the claims that are being made hold with respect to an implementation.

This document is a high level description of the syntax of
act specifications.
For a more formal treatment of the syntax, study the
definitions of [Untyped.hs](https://github.com/ethereum/act/blob/master/src/Untyped.hs).

## Types

The types of Act consist of three basic primitives:
Integers, Booleans and ByteStrings. Integers are unbounded,
with true integer operations. However, as our integer expressions
will often represent words in the EVM, we allow ourselves a slight
abuse of notation and denote by `uintN/intN` integers together with the
constraint that the value fits into a `uintN/intN`.

Using conventional ABI types for typing also allows us to specify
function signatures in a concise way.

As an example consider the specification of overflow safe addition:

```act
behaviour add of SafeMath
interface add(uint x, uint y)

iff in range uint

   x + y

returns x + y
```

In more verbose terms, this specification would read:

Given any pair of integers `x` and `y`, s.t. `0 <= x < 2^256` and
`0 <= y < 2^256`, an ABI encoded call to the contract `SafeMath`
with the signature `add(uint256,uint256)`, and `x` and `y`, will:

-   return `x + y`      if `0 <= x + y < 2^256`
-   revert              otherwise

## Constructor

A `constructor` specification is indicated by the
`constructor of <contractName>` header, as in:
```act
constructor of A
```

A constructor section consists of the following fields:

### interface

Specifying the arguments the constructor takes.
Example:
```act
interface constructor(address _owner)
```

### iff (optional)

The conditions that must be satisfied in order for the contract to be created.
These must be necessary and sufficient conditions, in the sense that if any
condition isn't met, the contract cannot be created.

Example:
```act
iff

CALLER == _owner
```


### creates
Defines the storage layout of the contract.

Example:
```act

creates

  uint256 totalSupply := _totalSupply
  mapping(address => uint) balanceOf :=  [CALLER := _totalSupply]
```

Storage variables can be either simple ABI types, mappings, or contracts types of contracts that are specified in the same file.

### Ensures (optional)

A list of predicates that should hold over the poststate. All references to storage
variables in `ensures` sections need to specify whether they talk about the variable's
value in the pre- or the poststate, by using `pre(x)` or `post(x)`.
Example:
```act

ensures

   (post(x) == _x) or (pre(x) == _x)
```

### Invariants (optional)

A list of predicates over the state of the contract that should hold before and after
every contract invocation:

```act
invariants

  totalSupply = initialSupply
  _k = x * y
```

## Behaviour

A `behaviour` specification is indicated by the
`behaviour of <contractName>` header, as in:
```act
behaviour of A
```

and consists of the following fields:


### interface

Specifying which method the behaviour refers to.
Example:
```act
interface transfer(address to, uint value)
```

### iff (optional)

The conditions that must be satisfied in order for the transition to apply.
These must be necessary and sufficient conditions, in the sense that if any
condition isn't met, a call to the given method must revert.

Example:
```act
iff

  balanceOf[CALLER] >= value
  CALLVALUE == 0
```

### state updates and returns

Each behaviour must specify the state changes that happens a result of
a valid call to the method, and its return argument, if any.
All references to storage variables in `returns` arguments need to
specify whether they talk about the variable's
value in the pre- or the poststate, by using `pre(x)` or `post(x)`.

Example:
```act

storage

  balanceOf[CALLER] => balanceOf[CALLER] - value
  balanceOf[to] => balanceOf[to] + value

returns post(balanceOf[CALLER])
```

### cases

State updates and returns can be split between a number of cases, as in:

```act
case to == CALLER:

   returns -1

case to =/= CALLER:

   storage
     balanceOf[CALLER] => balanceOf[CALLER] - value
     balanceOf[to] => balanceOf[to] + value

   returns post(balanceOf[CALLER])
```

Note that currently, either a `storage` or `returns` section, or both is required in every spec.

### Ensures (optional)

A list of predicates that should hold over the poststate.
Example:
```act

ensures

   x == _x
```

## Multiple contracts

Act supports defining multiple contracts in the same file. State
variables can have contract types and they can be initialized by
calling the corresponding constructor.  The state variables of some
contract can be accessed using dot notation `.`.

Example:

```
constructor of A
interface constructor()

creates
   uint x := 0

constructor of B
interface constructor()

creates
   A a := A()

behaviour remote of B
interface set_a(uint z)

iff
   CALLVALUE == 0

storage
   a.x => z
```


## Range predicates
Often, to accurately specify a contract, we need to assume that
arithmetic operations do not overflow. This is done with built-in
*in-range* predicates. For example, in the iff conditions of a
constructor of behaviour we can write


```
iff
   inRange(uint256, (a + b) - c)
   CALLVALUE =/= 0
```

meaning that all subexpressions of `(a + b) - c` will always be in the
range of a 256-bit integer and no overflow or underflow occurs.

Such in range predicates can be conditional, for example

```
CALLER =/= x => inRange(uint256, (a + b) - c)
```


To conveniently pack many in range predicates together Act provides an
alternative form of iff conditions

```
iff
   CALLVALUE =/= 0

iff in range uint256
   (a + b) - c
   d - e
```
