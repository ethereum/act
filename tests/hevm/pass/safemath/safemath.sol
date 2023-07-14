pragma solidity >=0.4.21;

contract SafeAdd {

    constructor () payable { }

    function add(uint x, uint y) public pure returns (uint) {
	return (x + y);
    }

    function mul(uint x, uint y) public pure returns (uint) {
	return (x * y);
    }

    function double(uint x) public pure returns (uint) {
	return (2*x);
    }

}
