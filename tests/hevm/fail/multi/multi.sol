contract A {
    uint x;

    constructor (uint z)  {
	x = z + 42;
    }

    function set_x(uint z) public {
	x = z;
    }
}

contract B {

    uint y;
    A a;

    constructor(uint v) {
	y = 0;
	a = new A(v);
    }
}
