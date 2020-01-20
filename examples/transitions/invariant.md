# Contract invariant, functions pre and post

```act
contract A

	x : uint256

invariants

	x <= 2
	x <= 1 {f, h}


property f_post of f

	pre(x) = 0 => post(x) = 1


property g_post of g

	pre(x) = 1 => post(x) = 2


property h_post of h

	pre(x) = 2 => post(x) = 0


behavior f of A
interface f()

case x == 0:
	x := 1

case _:
	noop

ensures

	x != 0


behavior g of A
interface g()

case x == 1:
	x := 2

case _:
	noop

ensures

	x != 1


behavior h of A
interface h()

case x == 2:
	x := 0

case _:
	noop

ensures

	x != 2
```
