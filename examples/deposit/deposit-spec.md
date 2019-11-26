# Background

This is a specification of the [Eth2.0 deposit contract](https://github.com/ethereum/eth2.0-specs/blob/dev/deposit_contract/contracts/validator_registration.v.py), based on previous work by Daejun Park.

The contract allows for participants to lock up at least 32 ether in order to become a validator on the eth2.0 chain. Their deposits are fitted into a sparse merkle tree allowing efficient inclusion proofs to be submitted to the beacon chain. In order to optimize storage and runtime efficiency, the contract implements a so called "incremental merkle tree algorithm" which only stores the "frontier" of the merkle tree, pictured as red nodes in the figure below. 
![Incremental merkle tree](https://github.com/ethereum/smart-contract-spec-lang/tree/bnfc/examples/deposit/inc_merkle_tree.png "Incremental merkle tree")
This provides sufficient information to calculate the root hash of the tree. In order to reconstruct the full tree, it is expected that nodes rely on calldata from previous transactions, or the events emitted by the contract.

# Specification

The two main functions of the contract are `deposit` and `get_deposit_root`.

## Deposit
```act
behaviour deposit of ValidatorRegistration
interface deposit(bytes[48] pubkey, bytes[32] withdrawal_credentials, bytes[96] signature, bytes32 deposit_data_root)

for all

   x : uint256

storage

    branch[index_of_first_one(deposit_count, 0)] |-> _ => sha256(
          sha256(
             sha256(pubkey ++ "0x00000000000000000000000000000000") ++ withdrawal_credentials)
          ++ sha256(to_bytes(CALLVALUE / 10^9, 64) ++ sha256(
             sha256(signature[0..64]) ++ sha256(signature[65..96] ++ "0x0000000000000000000000000000000000000000000000000000000000000000")))
             )
     deposit_count |-> x => x + 1

where

   index_of_first_one(N, M) = if N % 2 == 1 then M else index_of_first_one(N / 2, M + 1)

iff in range uint256

   x + 1
```

## Get deposit root

```act
behaviour get_deposit_root of ValidatorRegistration
interface get_deposit_root()

for all

   br    : bytes32[32]
   zeros : bytes32[32]

//This example begs for some list abstractions
storage
    
    branch |-> br
    zero_hashes |-> zeros
    deposit_count |-> x

returns sha256(hashLoR(br, zeros, deposit_count)
               ++ to_bytes(x, 64) ++ "0x000000000000000000000000000000000000000000000000")

where

    hashLoR(frontier, zs, count) = foldr (\(i, (br, z)) acc -> if deposit_count / 2^i % 2 == 1 then sha256(br, acc) else sha256(acc, z) $ zip [1..] $ zip zeros br
```

# Properties

The incremental merkle algorithm implemented by the functions `deposit` and `get_deposit_root` should be equivalent to a "naïve algorithm", which simply inserts deposits into the tree, storing every leaf node and hashes them to get the root. 
We can express this property as claim about a series of consecutive calls to deposit. 

In other words, given any finite list of calls, `[C_0, C_1, ... C_n]` to the contract, for every element whose calldata matches the function signature of the `deposit` function, if we put the argument of those calls in a sparse merkle tree, the root of that tree should be the same as what we would get from calling the `get_deposit_root` function.

More formally, our claim is the following. 

`Theorem (Incremental updating)`

For every list of calls `C = [C_0, C_1, ... C_n]` applied to the contracts initial state, let the sublist `D = [D | length(C.calldata) == 4 + 32 + 96 + 32 and C.calldata[0..4] == keccak256("deposit(bytes,bytes,bytes, bytes32)")]` consist of the valid calls to the `deposit` function. Then the partial merkle tree whose nodes up to `n` are given by `DepositData_root(D_i.calldata[4..])` has the same root as the result of a call to `get_deposit_root()`.

`Proof:`
Since the only calls that modify state are valid calls to `deposit`, it suffices to consider `D` to get the contract state after `C`. What remains to show is that the incremental merkle tree algorithm yields the same result as the root of a partial merkle tree. This has been demonstrated by Daejun in [https://github.com/runtimeverification/verified-smart-contracts/blob/deposit/deposit/formal-incremental-merkle-tree-algorithm.pdf].

Formal statement concept art:

```act
property inc_merkle of deposit

for all

    x : uint
    A : bytes[208][2^x]

have

    merkle_root(A) == get_deposit_root(apply([deposit(a) | a in A], initial_state))

where

    merkle_root(A) := ...
```

In the above, assume that `apply` is an act keyword. An alternative is to make every behaviour result in a stateful function, in which case `apply` is essentially a `fold`.
