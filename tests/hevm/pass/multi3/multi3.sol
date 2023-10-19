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

    function incr_z() public {
	z = z + 1;
    }

    function a_add_x(uint y) public {
	a.add_x(y);
    }
}

contract C {

    uint y;
    A a;
    B b;

    constructor(uint u) {
	y = 0;
	a = new A(u);
	b = new B(u);
    }

    function remote(uint z) public returns (uint) {
	b.incr_z();
	b.a_add_x(z);
	return z;
    }
}

