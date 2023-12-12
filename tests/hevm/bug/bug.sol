contract A {
    function bar(uint y) public returns (uint){
	return y;
    }
}

contract B {
    A a;

    constructor ()  {
	a = new A();
    }

    function foo() public returns (uint){
	a = new A();
	return 42;
    }
}
