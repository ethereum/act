contract A {
    uint x;

    constructor () {
	x = 0;
    }

    function f() external {
        x = 2;
    }
}
