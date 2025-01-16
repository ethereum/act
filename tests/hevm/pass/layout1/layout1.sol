contract A {
    uint128 x;
    uint128 y;
    
    constructor() {
        x = 0;
        y = 0;
    }

    function swap() external returns (uint) {

        x = 11;
        y = 42;

        return 1;
    }
}