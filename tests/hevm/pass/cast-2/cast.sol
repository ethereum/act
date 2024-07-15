pragma solidity >=0.8.0;

contract C {
    uint z;

    constructor(uint _z) {
	z = _z;
    }


    function setz(uint _z1) public {
	z = _z1;
    }
}


contract A {
    uint x;
    C c;
    
    constructor(uint _x) {
	x = _x;
	c = new C(42);
    }


    function getx() public returns (uint) {
	return x;
    }

    function setx(uint _x1) public {
	x = _x1;
    }

    function setc(uint _z1) public {
	c.setz(_z1);
    }

}


contract B {
    A a1;
    A a2;

    constructor(address x, address y) {
	a1 = A(x);
	a2 = A(y);
    }


    function upd() public {
	a1.setx(42);
	a2.setx(11);
	a1.setc(17);
    }

}
