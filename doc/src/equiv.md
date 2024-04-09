# Checking equivalence with EVM bytecode

EVM bytecode can be formally verified to implement an Act spec. This
means that each successful behavior of the bytecode should be covered
by the Act spect. To check equivalence the Act spec is translated to
Expr, the intermediate representation of HEVM, and the EVM bytecode is
symbolically executed to obtain its Expr representation. Then
equivalence can be checked with the equivalence checker of HEVM.

The Expr representation of an Act program is a list of *Success*
nodes, that contain the possible successful results of the
computation. The Expr representation of the EVM bytecode can also be
flattened to a list of result nodes from which we only keep the
successful executions, filtering out failed and partial execution
paths. An informative warning will be thrown when partial executions
are encountered.

A success node in Expr, `Success cond res storage`, is a leaf in the
Expr tree representation and contains the path conditions, `cond` that
lead to the leaf, the result buffer `res`, and the end state
`storage`.


## Equivalence checks 
To check equivalence between the two Expr representations the
following checks are performed. 

### Result equivalence
The two list of `Success` nodes are checked for equivalence using
the HEVM equivalence checker. For each pair of nodes in the two lists,
we check that for all inputs that satisfy the combined path conditions the
result and final storage the same. 

### Input space equivalence
Since the input space of the two lists is not necessarily exhaustive,
some inputs may lead to failed execution paths that are not
present in the list. We therefore need to check that the input space of the two
lists are the same. That is, there must not be inputs that satisfy
some path condition in the first list but not the second and vice verse. 

Say that the Act program has the Expr representation 
`[Success c1 r1 s1, ..., Success cn rn sn`
and the EVM bytecode has the Expr representation 
`[Success c1' r1' s1', ..., Success cn' rn' sn'`

then we need to check that `c1 \/ .. \/ cn <-> c1' \/ .. \/ cn'` that
is, we require that `c1 \/ .. \/ cn /\ ~ (c1' \/ .. \/ cn')` and `c1'
\/ .. \/ cn' /\ ~ (c1 \/ .. \/ cn)` are both unsatisfiable.

### Exhaustiveness checks for bytecode
TODO
