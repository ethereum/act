contract A {
    uint128 x;
    uint128 y;
    
    constructor() {
        x = 11;
        y = 42;
    }

    function swap() external returns (uint) {
        uint128 temp; 

        temp = x;
        x = y;
        y = temp;

        return 1;
    }
}
