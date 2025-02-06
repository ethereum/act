contract A {
    uint128 x;
    bool flag;
    uint32 u;
    uint8 z;
    uint128 y;
    uint256 i;

    constructor() {
        x = 11;
        flag = true;
        u = 17;
        z = 3;
        y = 42;
        i = 128;
    }

    function foo() external returns (uint) {

        uint128 tmp = x;

        x = y;
        y = tmp;
        z = 11;
        flag = !flag;

        return 1;
    }

    function set_flag(bool b) external {
        flag = b;
    }

    function get_flag() external returns (bool) {
        return flag;
    }

    function set_y_if_flag(uint128 v) external returns (uint) {
        if (flag) {
            y = v;
        }

        return 1;
    }
}