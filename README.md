Act
===

This project is an effort by several groups working on formal methods for
Ethereum smart contracts, aiming at creating a simple but effective language
to write formal specification.
It extends on the previous
[Act](https://github.com/dapphub/klab/blob/master/acts.md) project.

Some general features it hopes to achieve are:
- Simple structure and logic.
- Support writing properties on a high level (closer to Solidity/Vyper) as
  well as on the machine level.
- Cross-tool communication: Different tools might be able to generate
  different knowledge and use the specification language to exchange
  information.
- No attachment to a particular logic. If a tool wishes to support certain
  expressions, extensions can be written.

Everyone is encouraged to join/start discussions on issues and pull requests.


Language
========

Act specifications are functional descriptions of the behaviour of a smart
contract.  Take the following toy state machine written in Solidity as an
example:

```solidity
contract StateMachine {
    uint x;

    function f() public {
        if (x == 0)
            x = 1;
    }

    function g() public {
        if (x == 1)
            x = 0;
    }
}
```

The initial state is `x = 0`, and `x` can toggle between 1 and 0 by calling
functions `f` and `g`, respectively.

A simple specification for the program above could be the following Act:

```act
constructor of StateMachine
interface constructor()

creates
	uint256 x := 0

invariants
	x <= 1


behaviour f of StateMachine
interface f()

case x == 0:
	storage
		x => 1

ensures
	(post(x) == 0) or (post(x) == 1)


behaviour g of StateMachine
interface g()

case x == 1:
	storage
		x => 0

ensures
	(post(x) == 1) or (post(x) == 0)
```

The `case`s of a `behaviour` specify how storage changes as a result of calling
the function, and its return argument, if present. They make up the lowest
level description of the specification. Functions' pre and post conditions are
described in the `iff` and `ensures` sections, respectively. Contract
invariants specify relations between its storage variables that should remain
true for the entire lifetime of the contract. Return values can be specified
in `returns` sections. In `ensures` and `returns` sections, every name `x` which
reference a position in storage needs to be specified as either `pre(x)` or
`post(x)`, depending on whether the value of `x` before or after the transition
is meant.

More examples can be found in the `examples` directory.


Modular Approach
================

Act is designed to enable modular verification. Instead of checking
properties that might be too hard to prove from the bytecode, such as
contract invariants, we hope that it is easier to do that via multiple easier
steps:

1. Given a `behaviour`, show that implementation bytecode results in storage
   updates and return values as specified.
2. Given a `behaviour`, prove that the `post condition` described in the
   `ensures` section holds, assuming the `pre condition` described in the `iff`
   section.
3. Given a set of `behaviour`s, prove contract invariants.
4. Given `(transition system = "CONTRACT")`, show that arbitrary properties
   hold.

Note that steps 2, 3 and 4 can be done over Act only, without interaction with
the source code/bytecode. Reasoning about higher level properties outside the
source code/bytecode also makes it easier to apply different tools, which we
here refer to as `proof backends`.


Proof Backends
==============

We are currently working on three different proof backends:

	- Coq definitions
	- K specs
	- SMT theorems


The types of proofs that can be performed by the various backends can be understood in the following table:


| Proof type \ Backend          | HEVM    | KEVM | SMT                   | Coq     |
| ----------------------------- | ------- | ---- | --------------------- | ------- |
| Bytecode (with unknown calls) | Planned | ?    |                       |         |
| Bytecode                      | Planned | WIP  |                       |         |
| Poststate => postcondition    |         |      | WIP                   |         |
| Source level                  |         |      | Planned               |         |
| Contract level invariant      |         |      | [Done](./docs/smt.md) | WIP     |
| General higher properties     |         |      |                       | WIP     |


Infrastructure
==============

The grammar for the specification language is in the `src` repository. This
is the front end parsing of the language. Given a set of `act` behaviours
(transitions), one can generate a set of proof obligations as a JSON object.
For example, take the following simplified Token contract:

```solidity
contract Token {
	uint8 constant public decimals = 18;
	string public name;
	string public symbol;

	mapping (address => uint) public balanceOf;

	function mint(uint value) public {
		balanceOf[msg.sender] += value;
	}
}
```

The behaviour of function `mint` can be specified as the following Act:

```act
behaviour mint of Token
interface mint(uint value)

storage
	balanceOf[CALLER] => balanceOf[CALLER] + value
```

Parsing the Act gives us the generated proof obligations:

```JSON
[
  {
    "stateUpdates": {
      "Token": [
        {
          "location": {
            "arity": 2,
            "args": [
              "balanceOf",
              "CALLER"
            ],
            "symbol": "lookup"
          },
          "value": {
            "arity": 2,
            "args": [
              {
                "arity": 2,
                "args": [
                  "balanceOf",
                  "CALLER"
                ],
                "symbol": "lookup"
              },
              "value"
            ],
            "symbol": "+"
          }
        }
      ]
    },
    "name": "mint",
    "preConditions": [],
    "contract": "Token",
    "interface": "mint(uint256 value)",
    "returns": null
  }
]
```

Different proof backends can make use of this single JSON output without the
need to parse an Act, and apply its own techniques to try and answer the
proof obligations.


Building:
=========

With nix:

```sh
nix build -f default.nix exe
```

Developing:
-----------

Enter a nix-shell to get the dependencies of the project:
```sh
nix-shell
```
this gives all the necessary prerequisites for recompiling:
```sh
make compiler
```
or entering a `ghci` REPL:
```sh
make repl
```

To update the project dependencies run:
```sh
nix-shell --command niv update
```
