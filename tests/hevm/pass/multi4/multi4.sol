contract A {
    uint public x;

    constructor (uint z)  {
	x = z + 1;
    }

    function add_x(uint y) public {
	x = x + y;
    }
}

contract B {
    uint z;
    A a;

    constructor (uint i)  {
	z = i + 42;
	a = new A(i);
    }

    function foo() public {
	a = new A(42);
    }
}
