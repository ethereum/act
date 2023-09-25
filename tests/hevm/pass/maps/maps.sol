pragma solidity >=0.4.24;

contract Map {
    uint256 public val;
    mapping (uint => uint) public f;

    constructor () {
	val = 0;
        f[0] = 42;
    }


    function set(uint value, uint key) public returns (uint) {
	f[key] = value;

	return 1;
    }
}
