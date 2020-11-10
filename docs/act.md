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
definitions of [RefinedAst.hs](https://github.com/ethereum/act/blob/master/src/RefinedAst.hs).


## Contructor

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

### External storage changes (optional)

If the contract creation updates the state of other contracts,
they should be specified as:

```act
contract B
   x => x + 1

contract C
   y => y - 1
```

### Ensures (optional)

A list of predicates that should hold over the poststate.
Example:
```act

ensures

   x == _x
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

### cases and state updates

Each behaviour must specify the state changes that happens a result of 
a valid call to the method, and its return argument, if any.

This can be specified in two ways. Either directly, as in:

```act

storage

  balanceOf[CALLER] => balanceOf[CALLER] - value
  balanceOf[to] => balanceOf[to] + value

returns 1
```

or split between a number of cases, as in:

```act
case to == CALLER:

   returns 1
  
case to =/= CALLER:

   storage
     balanceOf[CALLER] => balanceOf[CALLER] - value
     balanceOf[to] => balanceOf[to] + value

   returns 1
```

### External storage changes (optional)

If the contract method updates the state of other contracts,
they should be specified as:

```act
contract B
   x => x + 1

contract C
   y => y - 1
```

### Ensures (optional)

A list of predicates that should hold over the poststate.
Example:
```act

ensures

   x == _x
```
