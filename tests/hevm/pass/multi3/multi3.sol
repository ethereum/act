contract A {
    uint public x;

    constructor (uint z)  {
	x = z + 1;
    }
}

contract B {
    uint z;

    constructor (uint i)  {
	z = i + 42;
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
}
