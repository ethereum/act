contract A {
    uint public x;

    constructor (uint z)  {
	x = z + 1;
    }

    function set_x(uint z) public {
	x = z;
    }
}

contract B {
    uint public z;

    constructor (uint i)  {
	z = i + 42;
    }
}

contract C {

    uint public y;
    A public a;
    B public b;

    constructor(uint u) {
	y = 0;
	a = new A(u);
	b = new B(u);
    }
}
