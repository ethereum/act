contract A {
    uint128 x;
    uint128 y;
    
    constructor() {
        x = 0;
        y = 0;
    }

    function swap() external returns (uint) {

        x = y;
        // y = x;

        return 1;
    }
}