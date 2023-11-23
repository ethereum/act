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

    uint y;
    A a;

    constructor(uint u) {
	y = 0;
	a = new A(u);
    }

    /* TODO */
    /* function remote(uint z) public { */
    /* 	a.set_x(z); */
    /* } */

    /* function multi(uint z) public { */
    /* 	y = 1; */
    /* 	a.set_x(z); */
    /* } */
}
