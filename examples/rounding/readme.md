# Rounding Error

Understanding the impact of rounding error in a smart contract is a critical task for secure smart
contract development.

There are two properties of interest:

- The direction of the rounding error (who loses out)
- The size of the rounding error (by how much do they lose)

For example in the case of a smart contract that holds a pool of tokens, it is a critical property
that any rounding error is always in favour of the pool. If this property does not hold the pool
will slowly bleed tokens as it is used.

The following procedure should allow us to automatically prove statements about the direction and
size of rounding error in an act behaviour:

- For every calculation involving a division encode the calculation as a two forumlae in `smt2`: one
  over the reals and one over the integers.
- assert some relation between the two forumlae (e.g. the expression over the integers is always
  less than or equal to the expression over the reals)
- assert that the difference between the two expression is never greater than some user provided
  constant.

For a manual example of a very similar procedure, see the [uniswap v1
model](https://github.com/runtimeverification/verified-smart-contracts/blob/uniswap/uniswap/x-y-k.pdf)
produced by Runtime Verification.

## Rounding Annotations

For a concrete syntax proposal, consider the following snippet from a smart contract implementing a
token pool (the full implementation can be seen [here](./Pool.sol), and it's act spec is
[here](./pool.act.md).

`exit` allows the caller to exchange `shares` pool shares for the proportional amount of the
underlying tokens.

```solidity
function exit(uint shares) external returns (uint amt0, uint amt1) {
    require(totalSupply > 0);

    amt0 = mul(token0.balanceOf(address(this)), shares) / totalSupply;
    amt1 = mul(token1.balanceOf(address(this)), shares) / totalSupply;

    burn(msg.sender, shares);
    token0.transfer(msg.sender, amt0);
    token1.transfer(msg.sender, amt1);
}
```

`exit` can be represented in act as follows. Note the **rounding annotations** (`:: (...)`) on the
storage blocks for `token0` and `token1`.

These annotations consist of two parts:

1. a relation to `exact`
2. a constant integer bound

They produce an `smt2` query encoding the following:

1. The given relation between the integer and real forms of the expression holds
2. The difference between the integer and real forms does not exceed `bound`

Additionally the act compiler can analyze all defined behaviours and throw a warning if there are
writes to storage involving division that do not have rounding annotations.

The annotations in the act below can be read as:

> The rounding error in `exit` is always in favour of the pool, and never exceeds 1 wei.

```act
behaviour exit of Pool
interface exit(uint shares)

iff

    CALLVALUE == 0
    totalSupply > 0

iff in range uint256

    token0.balanceOf[ACCT_ID] - amt0
    token0.balanceOf[CALLER]  + amt0

    token1.balanceOf[ACCT_ID] - amt1
    token1.balanceOf[CALLER]  + amt1

    token0.balanceOf[ACCT_ID] * shares
    token1.balanceOf[ACCT_ID] * shares

    balanceOf[CALLER] - shares

storage token0

    balanceOf[ACCT_ID] => balanceOf[ACCT_ID] - amt0 :: (>= exact, bound 1)
    balanceOf[CALLER]  => balanceOf[CALLER]  + amt0 :: (<= exact, bound 1)

storage token1

    balanceOf[ACCT_ID] => balanceOf[ACCT_ID] - amt1 :: (>= exact, bound 1)
    balanceOf[CALLER]  => balanceOf[CALLER]  + amt1 :: (<= exact, bound 1)

storage

    balanceOf[CALLER] => balanceOf[CALLER] - shares

where

    amt0 := (token0.balanceOf[ACCT_ID] * shares) / totalSupply
    amt1 := (token1.balanceOf[ACCT_ID] * shares) / totalSupply
```

## Potential Alternative Syntax

The rounding behaviour is a high level property of the transition system, and it may therefore be
desirable to seperate it syntacticaly from the raw behaviours.

It may also be possible to automatically derive the rounding annotations from some kind of high
level description, where the rounding properties on individual storage reads/writes can be computed
by the compiler.

Such a procedure seems potentially incomplete and error prone, and may obscure important details
from the visibility of developers and auditors.

The high level syntax could perhaps look something like the following:

```act
rounding of Pool

join

    for     ACCT_ID, bound 1
    against CALLER,  bound 1

exit

    for     ACCT_ID, bound 1
    against CALLER,  bound 1
```
