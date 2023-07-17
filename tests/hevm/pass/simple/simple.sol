contract A {
    mapping(uint=>uint) x;

    function f() external returns (uint) {
        x[0] = 1;
        return 1;
    }
}
