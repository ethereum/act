contract A {
    uint128 x;
    uint128 y;
    
    constructor() {
        x = 11;
        y = 42;
    }

    function swap() external returns (uint) {

        uint128 tmp = x;
        
        x = y;
        y = tmp;

        return 1;
    }
}