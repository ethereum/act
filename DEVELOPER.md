Building process uses nix.

To generate the haskell compiler, first a parser is generated using bnfc. 
This generates the modules `AbsAct` `LexAct` `ParAct` `ErrM` upon which the main file `Splitter.hs` depends.
