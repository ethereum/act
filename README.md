Act
===

This project is an effort by several groups working on formal methods for
Ethereum smart contracts, aiming at creating a simple but effective language
to write formal specification.
It extends on the previous
[Act](https://github.com/dapphub/klab/blob/master/acts.md) project.

Some general features it hopes to achieve are:
- Simple structure and logic.
- Support writing properties on a high level (closer to Solidity/Vyper) as
  well as on the machine level.
- Cross-tool communication: Different tools might be able to generate
  different knowledge and use the specification language to exchange
  information.
- No attachment to a particular logic. If a tool wishes to support certain
  expressions, extensions can be written.

Everyone is encouraged to join/start discussions on issues and pull requests.


Language
========

Act specifications are functional descriptions of the behaviour of a smart
contract.  Take the following toy state machine written in Solidity as an
example:

```sol
contract StateMachine {
    uint x;
  
    function f() public {      
        if (x == 0)
            x = 1;             
    }

    function g() public {
        if (x == 1)
            x = 0;
    }
}
```

The initial state is `x = 0`, and `x` can toggle between 1 and 0 by calling
functions `f` and `g`, respectively.

A simple specification for the program above could be the following Act:

```act
behaviour init of StateMachine
interface constructor()

creates
	uint256 x := 0

invariants
	x <= 1


behaviour f of StateMachine
interface f()

case x == 0:
	storage
		x => 1

case _:
	noop

ensures
	(x == 0) or (x == 1)


behaviour g of StateMachine
interface g()

case x == 1:
	storage:
		x => 0

case _:
	noop

ensures
	(x == 1) or (x == 0)
```

The `case`s of a `behaviour` specify how storage changes as a result of calling
the function, and its return argument, if present. They make up the lowest
level description of the specification. Functions pre and post conditions are
described in the `iff` and `ensures` sections, respectively. Contract
invariants specify relations between its storage variables that should remain
true for the entire lifetime of the contract.

More examples can be found in the `examples` directory.


Modular Approach
================

Act is designed to enable modular verification. Instead of checking
properties that might be too hard to prove from the bytecode, such as
contract invariants, we hope that it is easier to do that via multiple easier
steps:

1. Given a `behaviour`, show that implementation bytecode results in storage
   updates and return values as specified.
2. Given a `behaviour`, prove that the `post condition` described in the
   `ensures` section holds, assuming the `pre condition` described in the `iff`
   section.
3. Given a set of `behaviour`s, prove contract invariants.
4. Given `(transition system = "CONTRACT")`, show that arbitrary properties
   hold.

Note that steps 2, 3 and 4 can be done over Act only, without interaction
with the source code/bytecode. Checking that the code implements the
behaviour specification correctly should be much easier than proving that
certain post conditions or contract invariants hold. Besides, reasoning about
higher level properties outside the source code/bytecode also makes it easier
to apply different tools, which we here refer to as `proof backends`.


Proof Backends
==============

We are currently working on three different proof backends:

	- Coq definitions
	- K specs
	- SMT theorems


Infrastructure
==============

The grammar for the specification language is in the `src` repository. This
is the front end parsing of the language. Given a set of `act` behaviours
(transitions), one can generate a set of proof obligations as a JSON object.
For example, take the following Token contract:

```sol
contract Token {
    // --- ERC20 Data ---
    uint8   constant public decimals = 18;
    string  public name;
    string  public symbol;
    uint256 public totalSupply;

    mapping (address => uint)                      public balanceOf;
    mapping (address => mapping (address => uint)) public allowance;

    event Approval(address indexed holder, address indexed spender, uint value);
    event Transfer(address indexed from, address indexed to, uint value);

    function add(uint x, uint y) internal pure returns (uint z) {
        require((z = x + y) >= x, "math-add-overflow");
    }
    function sub(uint x, uint y) internal pure returns (uint z) {
        require((z = x - y) <= x, "math-sub-underflow");
    }

    constructor(string memory symbol_, string memory name_, string memory version_, uint256 chainId_) public {
        symbol = symbol_;
        name   = name_;
        totalSupply = _totalSupply;
        balances[msg.sender] = _totalSupply;
    }

    // --- Token ---
    function transfer(address to, uint value) public returns (bool) {
        transferFrom(msg.sender, to, value);
        return true;
    }
    function transferFrom(address from, address to, uint value)
        public returns (bool)
    {
        if (from != msg.sender && allowance[from][msg.sender] != uint(-1)) {
            allowance[from][msg.sender] = sub(allowance[from][msg.sender], value);
        }
        balanceOf[from] = sub(balanceOf[from], value);
        balanceOf[to] = add(balanceOf[to], value);
        emit Transfer(from, to, value);
        return true;
    }
    function approve(address spender, uint value) public returns (bool) {
        allowance[msg.sender][spender] = value;
        emit Approval(msg.sender, spender, value);
        return true;
    }
}
```

The behaviours of the constructor and the functions `transfer` and
`transferFrom` can be specified as the following Act:

```act
behaviour init of Token
interface constructor(string _symbol, string _name, string _version, uint _totalSupply)

creates
    string name         := _name
    string symbol       := _symbol
    uint256 totalSupply := _totalSupply
    mapping(address => uint) balanceOf :=  [CALLER := _totalSupply]
    mapping(address=>mapping(address=>uint)) allowance := []


behaviour transfer of Token
interface transfer(uint256 value, address to)

iff

   CALLVALUE == 0
   value <= balanceOf[CALLER]
   CALLER =/= to => balanceOf[to] + value < 2^256

case CALLER =/= to:

   storage

     balanceOf[CALLER] => balanceOf[CALLER] - value
     balanceOf[to]     => balanceOf[to] + value

   returns 1

case CALLER == to:

   returns 1

behaviour transferFrom of Token
interface transferFrom(address src, address dst, uint value)

iff

   value <= balanceOf[CALLER]
   src    =/= dst => balanceOf[dst] + value < 2^256
   CALLER =/= src => 0 <= allowance[src][CALLER] - value
   CALLVALUE == 0

case src =/= dst:

   case CALLER == src:

      storage

         balances[src] => balances[src] - value
         balances[dst] => balances[dst] + value

      returns 1

   case CALLER =/= src and allowance[src][CALLER] == 2^256 - 1:

      storage

         balances[src] => balances[src] - value
         balances[dst] => balances[dst] + value

      returns 1

   case _:

      storage

         allowance[src][CALLER] => allowance[src][CALLER] - value
         balances[src]          => balances[src] - value
         balances[dst]          => balances[dst] + value

      returns 1

case src == dst:

   returns 1
```

Parsing the Act gives us the generated proof obligations:

```JSON
[
  {
    "stateUpdates": {
      "Token": [
        {
          "location": {
            "arity": 2,
            "args": [
              "balanceOf",
              "CALLER"
            ],
            "symbol": "lookup"
          },
          "value": {
            "arity": 2,
            "args": [
              {
                "arity": 2,
                "args": [
                  "balanceOf",
                  "CALLER"
                ],
                "symbol": "lookup"
              },
              "value"
            ],
            "symbol": "+"
          }
        }
      ]
    },
    "name": "mint",
    "preConditions": [],
    "contract": "Token",
    "interface": "mint(uint256 value)",
    "returns": null
  }
]
```

Different proof backends can make use of this single JSON output without the
need to parse an Act, and apply its own techniques to try and answer the
proof obligations.


Building:
=========

With nix:

```sh
nix-build
```

without nix:

Install BNFC and cabal, then
```sh
make
```


Developing:
-----------

Enter a nix-shell to get the dependencies of the project:
```sh
nix-shell
```

If you need to modify the cabal file, run
```sh
cabal2nix src/act.cabal > src/default.nix
```
and then modify default.nix to have BNFC as a dependency and `preBuild = "make parser"`.
