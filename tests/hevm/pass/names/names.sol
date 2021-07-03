contract Names {
  mapping (bytes32 => address) public names;

  function register(bytes32 hash) payable external {
    require(msg.value >= 0.1 ether, "names/fee-not-provided");
    require(msg.sender != address(0), "names/no-zero-caller");
    require(names[hash] == address(0), "names/name-already-registered");
    names[hash] = msg.sender;
  }
}

