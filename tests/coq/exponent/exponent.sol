// implementation of an exponentiation process

contract Exponent {

    uint b;
    uint e;
    uint r;

    constructor(uint _b, uint _e) {
        require(e > 0);

        b = _b;
        e = _e;
        r = _b;
    }

    function exp() public {
        require(e > 1);
        require(b == 0 || (r * b) / b == r);    // safe mul
        require(e - 1 <= e);                    // safe sub

        r = r * b;
        e = e - 1;
    }

}

