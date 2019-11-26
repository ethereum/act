# add of safemath

```act
behaviour add of SafeAdd
interface add(x : uint256, y : uint256)

iff in range uint256

    X + Y

iff

    VCallValue == 0

returns X + Y
```
