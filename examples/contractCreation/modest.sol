contract Modest {
  uint x = 1;
  address owner;
  constructor() {
    owner = msg.sender;
  }
}
