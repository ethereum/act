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
The grammar for the specification language is in the `src` repository. This is the front end parsing of the language. Given a set of `act` behaviours (transitions), one can generate a set of proof obligations, expressed as a JSON object:
```json
[{"name": "Transfer_case0",
 "contract": "Token",
 "status_code": "EVMC_SUCCESS",
 "return": [],
 "case": "pass",
 "bytecode": "0xdeadbeef",
 "storageLayout": "probably",
 "interface": "the same as in the spec",
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
   "CALLER =/= to",                                 // case specific
   "CALLVALUE == 0",                                // from iff
   "value <= balanceOf[CALLER]",
   "CALLER =/= to => balanceOf[to] + value < 2^256",//
   "0 <= to",                                       //from type restrictions
   "to < 2^160",
   "0 <= v0",
   "v0 < 2^256",
   "0 <= v1",
   "v0 < 2^256",
   "v0 - amount <= v0",
   "v0 - amount < 2^256",
   "v1 + amount <= v0",
   "v1 + amount < 2^256"
 ],
 "postcondition": []
 },
{"name": "Transfer_case1",
 "contract": "Token",
 "status_code": "EVMC_SUCCESS",
 "return": [],
 "case": "pass",
 "bytecode": "0xdeadbeef",
 "interface": "the same as in the spec",
 "storage_pre": [],
 "storage_post": [],
 "precondition": [
   "CALLER == to",                                  // case specific
   "CALLVALUE == 0",                                // from iff
   "value <= balanceOf[CALLER]",
   "CALLER =/= to => balanceOf[to] + value < 2^256",//
   "0 <= to",                                       //from type restrictions
   "to < 2^160",
   "0 <= v0",
   "v0 < 2^256",
   "0 <= v1",
   "v0 < 2^256",
   "v0 - amount <= v0",
   "v0 - amount < 2^256",
   "v1 + amount <= v0",
   "v1 + amount < 2^256"
 ],
 "postcondition": []
}]
```


Multiple levels of proofs:
--------------------------

i) Given "behaviour case", show that poststorage is implemented by the bytecode.
ii) Given behaviour, prove that the postcondition holds.
iii) Given postconditions, show contract invariant property
iiii) Given (transition system = "CONTRACT"), show that arbitrary property holds

Developing:
-----------

The front-end parser is built using `bnfc`. For a reliable building experience, use `nix`:
```sh
nix-shell shell.nix
make test-parse
```
