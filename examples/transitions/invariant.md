# Contract invariant, functions pre and post

```act
contract A

storage

	x : uint256

invariants

	x <= 2
	x <= 1 {f, h}


behavior f of A
interface f()

ensures

	x != 0



behavior g of A
interface g()

ensures

	x != 1


behavior h of A
interface h()

ensures

	x != 2
```
