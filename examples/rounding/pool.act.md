# Pool

## Constructor

```act
behaviour init of Pool
interface constructor(address _token0, address _token1)

creates

    address token0 := _token0
    address token1 := _token1

    uint256 public totalSupply := 0
    mapping (address => uint) balanceOf := []
```

## Transfer

`transfer` allows the caller to transfer `wad` pool shares to `dst`.

`transfer` fails if:

  - any of the calculations overflow
  - ether is provided in the call

Self transfers are allowed, provided the caller has more than `wad` pool shares.

```act
behaviour transfer of Pool
interface transfer(address dst, uint wad)

iff

   CALLVALUE == 0
   wad <= balanceOf[CALLER]
   CALLER =/= to => balanceOf[dst] + wad < 2^256

case CALLER =/= to:

   storage

       balanceOf[CALLER] => balanceOf[CALLER] - wad
       balanceOf[dst]    => balanceOf[dst]    + wad

   returns 1

case CALLER == to:

   returns 1
```

## Join

`join` allows the caller to exchange `amt0` and `amt1` tokens for some amount of pool shares. The
exact amount of pool shares minted depends on the state of the pool at the time of the call.

`join` fails if:

- any calculation overflows
- ether is provided in the call

```act
behaviour join of Pool
interface join(uint amt0, uint amt1)

iff

    CALLVALUE == 0

iff in range uint256

    token0.balanceOf[CALLER] - amt0
    token0.balanceOf[ACCT_ID] + amt0

    token1.balanceOf[CALLER] - amt1
    token1.balanceOf[ACCT_ID] + amt1

storage token0

    balanceOf[CALLER]  => balanceOf[CALLER]  - amt0
    balanceOf[ACCT_ID] => balanceOf[ACCT_ID] + amt0

storage token1

    balanceOf[CALLER]  => balanceOf[CALLER]  - amt0
    balanceOf[ACCT_ID] => balanceOf[ACCT_ID] + amt0

case totalSupply == 0:

    iff in range uint256

        balanceOf[CALLER] + min(amt0, amt1)
        totalSupply + min(amt0, amt1)

    storage

        balanceOf[CALLER] => balanceOf[CALLER] + min(amt0, amt1)

    returns min(amt0, amt1)

case totalSupply =/= 0:

    iff in range uint256

        totalSupply * amt0
        totalSupply * amt1

        balanceOf[CALLER] + sharesSubsq
        totalSupply + sharesSubsq

    storage

        balanceOf[CALLER] => balanceOf[CALLER] + sharesSubsq :: (<= exact, bound 1)

    returns sharesSubsq

where

    sharesSubsq := min(
        (totalSupply * amt0) / token0.balanceOf[ACCT_ID],
        (totalSupply * amt1) / token1.balanceOf[ACCT_ID],
    )
```

## Exit

`exit` allows the callers to exchange `shares` pool shares for the proportional amount of the
underlying tokens.

`exit` fails if:

- any calculations overflow
- totalSupply is 0
- ether is provided in the call

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

rounding

    for ACCT_ID, bound 1
    against CALLER, bound 1
```
