contract Map {
    uint128 public val;
    mapping (uint => uint128) public f;
    mapping (uint128 => bool) public g;
    
    constructor() {
        val = 11;
        f[11] = 42;
        g[22] = true;
        g[1] = false;
        f[42] = 1;
    }

    function setf(uint128 value, uint key) external returns (uint) {
        f[key] = value;
        return 1;
    }

    function setg(bool value, uint128 key) external returns (uint) {
        g[key] = value;
        return 1;
    }
}