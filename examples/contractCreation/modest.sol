contract Modest {
  uint x;
  address owner;
  constructor() {
    owner = msg.sender;
  }
}
