
// simple example of something that will require interactive proof
// we want to show that f and g maintain the invariant xy = z

pragma solidity ^0.5.15;
pragma experimental SMTChecker;

contract Homogeneous {

    uint x;
    uint y;
    uint z;

    constructor () public {
        x = 3;
        y = 5;
        z = 15;
    }
    
    function f (uint scalar) public {
        require (x * scalar > x);
        require (z * scalar > z);
        x = x * scalar;
        z = z * scalar;
        assert (x * y == z);
    }

    function g (uint scalar) public {
        require (y * scalar > y);
        require (z * scalar > z);
        y = y * scalar;
        z = z * scalar;
        assert (x * y == z);
    }
}
