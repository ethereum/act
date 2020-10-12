// Copyright (C) 2020 Martin Lundfall

// This program is free software: you can redistribute it and/or modify
// it under the terms of the GNU Affero General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.
//
// This program is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU Affero General Public License for more details.
//
// You should have received a copy of the GNU Affero General Public License
// along with this program.  If not, see <https://www.gnu.org/licenses/>.

pragma solidity >=0.4.24;

contract Token {
    // --- ERC20 Data ---
    uint8   constant public decimals = 18;
    string  public name;
    string  public symbol;
    uint256 public totalSupply;

    mapping (address => uint)                      public balanceOf;
    mapping (address => mapping (address => uint)) public allowance;

    event Approval(address indexed holder, address indexed spender, uint value);
    event Transfer(address indexed from, address indexed to, uint value);

    function add(uint x, uint y) internal pure returns (uint z) {
        require((z = x + y) >= x, "math-add-overflow");
    }
    function sub(uint x, uint y) internal pure returns (uint z) {
        require((z = x - y) <= x, "math-sub-underflow");
    }

    constructor(string memory symbol_, string memory name_, string memory version_, uint256 chainId_, uint _totalSupply) public {
        symbol = symbol_;
        name   = name_;
        totalSupply = _totalSupply;
        balanceOf[msg.sender] = _totalSupply;
    }

    // --- Token ---
    function transfer(address to, uint value) public returns (bool) {
        transferFrom(msg.sender, to, value);
        return true;
    }
    function transferFrom(address from, address to, uint value)
        public returns (bool)
    {
        if (from != msg.sender && allowance[from][msg.sender] != uint(-1)) {
            allowance[from][msg.sender] = sub(allowance[from][msg.sender], value);
        }
        balanceOf[from] = sub(balanceOf[from], value);
        balanceOf[to] = add(balanceOf[to], value);
        emit Transfer(from, to, value);
        return true;
    }
    function approve(address spender, uint value) public returns (bool) {
        allowance[msg.sender][spender] = value;
        emit Approval(msg.sender, spender, value);
        return true;
    }
}
