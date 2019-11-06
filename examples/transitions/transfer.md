# Transfer function a la ERC20

```act
behaviour transfer of Token
interface transfer(uint256 value, address to)

storage

     balanceOf[CALLER] => balanceOf[CALLER] - value
     balanceOf[to] => balanceOf[to] + value

iff in range uint256

     balanceOf[CALLER] - value
     balanceOf[to] + value

iff

     CALLVALUE == 0

if
     CALLER =/= to
```
