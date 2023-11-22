# Checking equivalence with EVM bytecode

EVM bytecode can be formally verified to implement an Act spec. This
means that each successful end state of the bytecode should be covered
by the Act spect. To check equivalence the Act spec is translated to
`Expr`, the intermediate representation of hevm, and the EVM bytecode
is symbolically executed to obtain its `Expr` representation. Then
equivalence can be checked with the equivalence checker of hevm.

The `Expr` representation of an Act program is a list of *Success*
nodes, that contain all possible results of the
computation.
%
The `Expr` representation of the EVM bytecode can also be
flattened to a list of result nodes from which we only keep the
successful executions, filtering out failed and partial execution
paths. An informative warning will be thrown when partial executions
are encountered.

A success node in `Expr`, `Success cond res storage`, is a leaf in the
`Expr` tree representation and contains the path conditions, `cond`
that lead to the leaf, the result buffer `res`, and the end final
storage `storage`.




## Equivalence checks
For each constructor and behavior in the Act spec
we perform the following

1. translate it to its `Expr` representation
2. find the corresponing bahavior in the bytecode, by doing symbolic
execution using the calldata the corresponds to the desired
behavior. This will return an `Expr` list of end states that
corresponds to this constructor/behaviour.

Then for each behaviour we check the following.

### Result equivalence
The two list of `Success` nodes are checked for equivalence using the
HEVM equivalence checker. For each pair of nodes in the two lists, we
check that for all inputs that satisfy the path conditions of both
lists the result and final state (return and storage) must be the
same.

### Input space equivalence
We also need to check that the path conditions that may lead to this
behavior are the same in both list.
That is, there must not be inputs that satisfy
some path condition in the first list but not the second and vice verse.

Say that the Act program has the Expr representation
`[Success c1 r1 s1, ..., Success cn rn sn`
and the the EVM bytecode has the Expr representation
`[Success c1' r1' s1', ..., Success cn' rn' sn'`

then we need to check that `c1 \/ .. \/ cn <-> c1' \/ .. \/ cn'`.
We require therefore require that `c1 \/ .. \/ cn /\ ~ (c1' \/ .. \/ cn')` and `c1'
\/ .. \/ cn' /\ ~ (c1 \/ .. \/ cn)` are both unsatisfiable.

### Result equivalence
The two list of `Success` nodes are checked for equivalence using the
HEVM equivalence checker. For each pair of nodes in thedekfunction selector
different from those present in Act is unsatisfiable.  If these
assertions were satisfiable, then it must be that there is a function
in the bytecode that produces successful end states in it is not
covered by the spec.


## Multiple contracts
If the contract creates and interacts with other contracts, then
equivalence checking becaumes more compilated.


### Contructors
