// SPDX-License-Identifier: AGPL-3.0-only
pragma solidity ^0.6.12;

interface ERC20 {
    function balanceOf(address usr) external view returns (uint256);
    function transfer(address usr, uint256 amt) external returns (bool);
    function transferFrom(address src, address dst, uint256 amt) external returns (bool);
}


contract Pool {
    // --- Data ---
    string  public constant name = "Token";
    string  public constant symbol = "TKN";
    uint8   public constant decimals = 18;

    ERC20 immutable public token0;
    ERC20 immutable public token1;

    uint256 public totalSupply;
    mapping (address => uint) public balanceOf;

    event Transfer(address indexed src, address indexed dst, uint wad);

    // --- Math ---
    function add(uint x, uint y) internal pure returns (uint z) {
        require((z = x + y) >= x);
    }
    function sub(uint x, uint y) internal pure returns (uint z) {
        require((z = x - y) <= x);
    }
    function mul(uint x, uint y) internal pure returns (uint z) {
        require(y == 0 || (z = x * y) / y == x);
    }
    function min(uint x, uint y) internal pure returns (uint z) {
        z = x < y ? x : y;
    }

    // --- Init ---
    constructor(address _token0, address _token1) public {
        token0 = ERC20(_token0);
        token1 = ERC20(_token1);
    }

    // --- Token ---
    function transfer(address dst, uint wad) external returns (bool) {
        balanceOf[msg.sender] = sub(balanceOf[msg.sender], wad);
        balanceOf[dst] = add(balanceOf[dst], wad);
        emit Transfer(msg.sender, dst, wad);
        return true;
    }

    function mint(address usr, uint wad) internal {
        balanceOf[usr] = add(balanceOf[usr], wad);
        totalSupply = add(totalSupply, wad);
        emit Transfer(address(0), usr, wad);
    }
    function burn(address usr, uint wad) internal {
        balanceOf[usr] = sub(balanceOf[usr], wad);
        totalSupply = sub(totalSupply, wad);
        emit Transfer(usr, address(0), wad);
    }

    // --- Join / Exit ---
    function join(uint amt0, uint amt1) external returns (uint shares) {
        token0.transferFrom(msg.sender, address(this), amt0);
        token1.transferFrom(msg.sender, address(this), amt1);

        if (totalSupply == 0) {
            shares = min(amt0, amt1);
        } else {
            shares = min(
                mul(totalSupply, amt0) / token0.balanceOf(address(this)),
                mul(totalSupply, amt1) / token1.balanceOf(address(this))
            );
        }

        mint(msg.sender, shares);
    }
    function exit(uint shares) external returns (uint amt0, uint amt1) {
        require(totalSupply > 0);

        amt0 = mul(token0.balanceOf(address(this)), shares) / totalSupply;
        amt1 = mul(token1.balanceOf(address(this)), shares) / totalSupply;

        burn(msg.sender, shares);
        token0.transfer(msg.sender, amt0);
        token1.transfer(msg.sender, amt1);
    }
}
