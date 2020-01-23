First, build the haskell parser by executing

```sh
nix-shell --command 'make build-hs' --pure    
```
in the main directory.

Then, build the rest of the compiler infrastructure with:
```sh
nix-shell --command 'cabal new-build' --pure 
```
executed in the `src/haskell` subdir.

Try executing on the `smoke.act` file, by running
```sh
./src/haskell/dist-newstyle/build/x86_64-linux/ghc-8.6.5/act-0.1.0.0/x/act/build/act/act ./tests/smoke/smoke.act
```
in the main directory.

Ideas welcome on how to improve this process.
