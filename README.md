# Act

Act is a formal specification language, designed to allow for the construction of an exhaustive,
mathematically rigorous description of evm programs. Act allows diverse toolchains to interoperate
on a single specification, with each generating and exchanging different kinds of knowledge. It has
a built-in analysis engine that can automatically prove properties about the specification itself,
as well as an integrated symbolic execution engine (based on hevm) that can prove equivalence
between a specification and a given bytecode object. Finally, specifications can be exported into
higher level reasoning tools (e.g. theorem provers, economic analysis tooling), allowing for the
verification of properties of almost arbitrary complexity, all with a proof chain right down to the
bytecode level.

It extends on the previous [Act](https://github.com/dapphub/klab/blob/master/acts.md) project.

More in depth documentation can be found in [The Act Book](https://ethereum.github.io/act/).

# Building

With nix:

```sh
nix build
```

# Developing

Enter a nix-shell to get the dependencies of the project:

```sh
nix develop
```

you can then use `cabal` as normal:

```sh
cd src
cabal build # build
cabal repl  # enter a repl instance
```

to execute the unit tests:

```sh
make test # run all tests
cd src && cabal v2-test # run haskell tests
```

To update the project dependencies run:

```sh
nix flake update
```
