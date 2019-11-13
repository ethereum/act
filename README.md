Smart Contract Specification Language
=====================================

This project is an effort by several groups working on formal methods for Ethereum smart contracts, aiming at creating a simple but effective language to write formal specification.

Some general features it hopes to achieve are:
- Simple structure and logic.
- Support writing properties on a high level (closer to Solidity/Vyper) as well as on the machine level.
- Cross-tool communication: Different tools might be able to generate different knowledge and use the specification language to exchange information.
- No attachment to a particular logic. If a tool wishes to support certain expressions, extensions can be written.

Everyone is encouraged to join/start discussions on issues and pull requests.

Starting Point
==============

The [Act](https://github.com/dapphub/klab/blob/master/acts.md) specification language already matches some of the desired features: It has a simple structure, simple logic, and supports properties written for EVM bytecode.

It is currently being used as the starting point for this project, requiring few modifications to the structure and syntax such that it can also support high level properties.

Infrastructure
==============
The grammar for the specification language is in the `src` repository. This is the front end parsing of the language. Given set of `act` behaviours (transitions), one can generate a set of proof obligations, expressed as a json object:

TODO: how to express variable names and the internal `AST` nodes?
```json
{"name": "Transfer_from_diff",
 "contract": "Token",
 "case": "pass",
 "variables": {
   "v0": "int",
   "v1": "int",
   "v2": "int",
   "v3": "bytes",
   "amount": "int",
   "to": "int"
   },
 "calldata": "0xa9059cbb ++ v3 ++ as_bytes(to) ++ as_bytes(amount)"
 "storage_pre": [
     {"type": "uint256",
      "name": "balanceOf[msg.sender]",
      "value": "v0"
     },
     {"type": "uint256",
      "name": "balanceOf[to]",
      "value": "v1"
     }
 ],
 "storage_post": [
     {"type": "uint256",
      "name": "balanceOf[msg.sender]",
      "value": "v0 - amount"
     },
     {"type": "uint256",
      "name": "balanceOf[to]",
      "value": "v1 + amount"
     }
 ],
 "precondition": [
   "0 <= to",
   "to < 2^160",
   "0 <= v0",
   "v0 < 2^256",
   "0 <= v1",
   "v0 < 2^256",
   "v0 - amount <= v0",
   "v0 - amount < 2^256",
   "v1 + amount <= v0",
   "v1 + amount < 2^256"
 ]
}
```
