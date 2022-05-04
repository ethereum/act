# Act

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

More in depth documentation can be found in [The Act Book](https://ethereum.github.io/act/).

# Building

With nix:

```sh
nix build -f default.nix exe
```

# Developing

Enter a nix-shell to get the dependencies of the project:

```sh
nix-shell
```

you can then use `cabal` as normal:

```sh
cd src
cabal v2-build # build
cabal v2-repl  # enter a repl instance
```

to execute the unit tests:

```sh
make test # run all tests
cd src && cabal v2-test # run haskell tests
```

To update the project dependencies run:
```sh
nix-shell --command niv update
```
