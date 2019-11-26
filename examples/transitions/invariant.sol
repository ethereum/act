contract C {
    uint x;
  
    function f() public {      
        if (x == 0)
            x = 1;             
    }

    function g() public {
        if (x == 1)
            x = 2;
    }

    function h() public {
        if (x == 2)
            x = 0;
    }
}
