contract A {
    uint x;

    constructor ()  {
	x = 0;
    }

    function set_x(uint z) public {
	x = z;
    }
}

contract B {

    uint y;
    A a;

    constructor() {
	y = 0;
	a = new A();
    }

    function remote(uint z) public returns (uint){
	a.set_x(z);
	return 0;
    }

    function multi(uint z) public {
	y = z;
	a.set_x(42);
    }
}
