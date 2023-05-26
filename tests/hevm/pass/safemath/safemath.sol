pragma solidity >=0.4.21;

contract SafeAdd {
    function add(uint x, uint y) public pure returns (uint z) {
        require((z = x + y) >= x);
    }
    
    function mul(uint x, uint y) public pure returns (uint z) {
        require((z = x * y) >= x);
    }

    function double(uint x) public pure returns (uint z) {
	require((z = 2 * x) >= x);
    }

}
