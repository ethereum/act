The syntax of the `act` specification language is defined using [BNFC](https://github.com/BNFC/bnfc) in the file [act.bf](./act.bf), which can automatically parse specifications into ASTs into a myriad of languages, including C++, Haskell and Java to name a few.

For example, the [haskell directory](./haskell) is generated through
```sh
bnfc -m -haskell act.bf
make
```
