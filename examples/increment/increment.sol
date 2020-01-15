pragma solidity ^0.5.11;

contract Increment {

    uint x;

    constructor() public {
        x = 2;
    }
    
    function incr() public {
        if (x + 1 > x)
            x = x + 1;
    }
}
