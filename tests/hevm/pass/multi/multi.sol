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

    /* function remote(uint z) public { */
    /* 	a.set_x(z); */
    /* } */

    /* function multi(uint z) public { */
    /* 	y = 1; */
    /* 	a.set_x(z); */
    /* } */
}
