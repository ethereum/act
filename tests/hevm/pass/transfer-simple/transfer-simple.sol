pragma solidity >=0.8.0;

contract Token {
    mapping (address => uint) public balanceOf;

    constructor(uint _totalSupply) {
        balanceOf[msg.sender] = _totalSupply;
    }


    function transfer(uint256 value, address to) public returns (uint) {
	    balanceOf[msg.sender] = balanceOf[msg.sender] - value;
        balanceOf[to] = balanceOf[to] + value;
        return 1;
    }

}
