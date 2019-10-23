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
