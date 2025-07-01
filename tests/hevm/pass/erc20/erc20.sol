pragma solidity >=0.8.0;

contract Token {
    uint256 public totalSupply;
    mapping (address => uint256) public balanceOf;
    mapping (address => mapping (address => uint256)) public allowance;

    constructor(uint256 _totalSupply) {
        totalSupply = _totalSupply;
        balanceOf[msg.sender] = _totalSupply;
    }


    function approve(address spender, uint256 value) public returns (bool) {
        if(spender != msg.sender) {
            allowance[msg.sender][spender] = value;
        }
        return true;
    }

    function transfer(uint256 value, address to) public returns (bool) {
        balanceOf[msg.sender] = balanceOf[msg.sender] - value;
        balanceOf[to] = balanceOf[to] + value;
        return true;
    }

    function transferFrom(address from, address to, uint256 value) public returns (bool) {
        if(from != msg.sender && allowance[from][msg.sender] != type(uint256).max) {
            allowance[from][msg.sender] = allowance[from][msg.sender] - value;
        }
        balanceOf[from] = balanceOf[from] - value;
        balanceOf[to] = balanceOf[to] + value;
        return true;
    }

    function burn(uint256 value) public returns (bool) {
        totalSupply = totalSupply - value;
        balanceOf[msg.sender] = balanceOf[msg.sender] - value;
        return true;
    }

    function burnFrom(address account, uint256 value) public returns (bool) {
        if(account != msg.sender && allowance[account][msg.sender] != type(uint256).max) {
            allowance[account][msg.sender] = allowance[account][msg.sender] - value;
        }
        totalSupply = totalSupply - value;
        balanceOf[account] = balanceOf[account] - value;
        return true;
    }

    function mint(address account, uint256 value) public returns (bool) {
        totalSupply = totalSupply + value;
        balanceOf[account] = balanceOf[account] + value;
        return true;
    }
}
