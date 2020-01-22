contract A {
  uint x;
  constructor() {
    x = 1;
  }
  function set(uint _x) {
    x = _x;
  }
}

contract B {
  A a;
  function set_remote(uint _x) {
    a.set(_x);
  }

  function create_a() {
    a = new A();
  }
}
