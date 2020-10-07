contract StateMachine {
    uint x;
  
    function f() public {      
        require(x == 0);
        x = 1;             
    }

    function g() public {
        require(x == 1);
        x = 2;
    }

    function h() public {
        require(x == 2);
        x = 0;
    }
}
