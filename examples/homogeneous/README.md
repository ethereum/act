# Contract invariants - model checking and proof assistant methods

The majority of the formal verification work that has been employed in practice so far in the ethereum ecosystem has been dealing with _functional correctness_, that is, given a specification of how a contract method should update the state, or an explicit assertion in the body of a method, demonstrate that the implementation correctly matches this specification or satisfies the assertion made. This can be done on an EVM level using tools like [KEVM](https://www.ideals.illinois.edu/handle/2142/97207) or on the solidity level using the [builtin smt-checker](https://github.com/leonardoalt/text/blob/master/solidity_isola_2018/main.pdf) or [solc-verify](https://arxiv.org/abs/1907.04262).

But often, the most crucial elements of how the smart contract behaves arise out of the interplay between its different functions, and its essence is best captured through a set of _invariant properties_, i.e. a predicate over its state variables which should hold before and after every function call. Some tools can already prove simple invariants, but struggle with invariants containing non-linear arithmetic expressions. 

## Linear invariants

Here is an example of an invariant provable by solc-verify
(solc-verfiy)
```sol
pragma solidity >=0.5.0;

/**
 * @notice invariant __verifier_sum_uint(balances) <= address(this).balance
 */
contract SimpleBank {
    mapping(address=>uint) balances;

    function deposit() public payable {
        balances[msg.sender] += msg.value;
    }

    function withdraw(uint256 amount) public {
        require(balances[msg.sender] > amount);
        balances[msg.sender] -= amount;
        bool ok;
        (ok, ) = msg.sender.call.value(amount)(""); // No reentrancy attack
        if (!ok) revert();
    }
}
```

and here is an example by the smt-checker:
```sol
pragma experimental SMTChecker;

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

	// This function shows that (x < 9) is not inductive and
	// a stronger invariant is needed to be found.
	// (x < 3) is the one found in the end.
	function j() public {
		if (x == 7)
			x = 100;
	}

	function i() public view {
		assert(x < 9);
	}
}
```
The smt-checker can in some cases also automatically infer invariants. The resulting horn query can be simplified to [something like this](./statemachinequery.smt2).

The examples above are easy for SMT solvers to reason about, since they deal with expressions of [linear arithmetic](https://cse-wiki.unl.edu/wiki/images/0/04/DecisionProcedure-Chapter5a.pdf). Linear arithmetic expressions can contain any valid combination of the symbols `<, <=, and, or, ==, +, -`, but they can crucially not contain multiplication between variables.

## Non-linear invariants

Here is a simple example contract with an invariant `x * y == z` that the smt-checker is unable to prove in its current form:
```sol
pragma solidity ^0.5.15;
pragma experimental SMTChecker;

contract Homogeneous {

    uint x;
    uint y;
    uint z;

    constructor () public {
        x = 3;
        y = 5;
        z = 15;
    }
    
    function f (uint scalar) public {
        require (x * scalar > x);
        require (z * scalar > z);
        x = x * scalar;
        z = z * scalar;
        assert (x * y == z);
    }

    function g (uint scalar) public {
        require (y * scalar > y);
        require (z * scalar > z);
        y = y * scalar;
        z = z * scalar;
        assert (x * y == z);
    }
}
```

The smt-checker encodes this using _constrained horn clauses_ and ends up with a Horn query that can be simplified to the following:

```smt2
(declare-rel state (Int Int Int))
(declare-rel error ())

(define-fun f ((x_pre Int) (y_pre Int) (z_pre Int) (scalar Int)
               (x_post Int) (y_post Int) (z_post Int)) Bool
  (and (>= scalar 1) (= x_post (* x_pre scalar)) (= z_post (* z_pre scalar)) (= y_pre y_post)))

(define-fun g ((x_pre Int) (y_pre Int) (z_pre Int) (scalar Int) (x_post Int) (y_post Int) (z_post Int)) Bool (and (>= scalar 1) (= y_post (* y_pre scalar)) (= z_post (* z_pre scalar)) (= x_pre x_post)))

(define-fun invariant ((x Int) (y Int) (z Int)) Bool (= (* x y) z))

(declare-var x_pre Int)
(declare-var x_post Int)
(declare-var y_pre Int)
(declare-var y_post Int)
(declare-var z_pre Int)
(declare-var z_post Int)
(declare-var scalar Int)

(rule (state 3 5 15))

(rule
(=>
    (and
     (state x_pre y_pre z_pre)
     (<= 0 x_pre)
     (<= 0 y_pre)
     (<= 0 z_pre)
     (<= 0 scalar)
     (or
      (f x_pre y_pre z_pre scalar x_post y_post z_post)
      (g x_pre y_pre z_pre scalar x_post y_post z_post)
      )
     )
    (state x_post y_post z_post)
))

(rule
(=>
    (and
        (state x_pre y_pre z_pre)
        (not (invariant x_pre y_pre z_pre))
    )
    error
))

(query error :print-certificate true)
```

The smt-checker uses Spacer to solve Horn queries. Spacer is distributed inside the theorem prover z3.
The last line asks the Horn solver whether the relation `error` is reachable, a relation that will only hold true if we can end up in a state where the invariant is violated.

Given this Horn query, z3 simply times out, as does the smt-checker given the contract above. The induction combined with the non-linear arithmetic expressions are beyond the reach of the tactics employed by the solver for constrained horn clauses.

However, if we simplify the Horn query to an SMT theorem so as to not model the full transition system implied by the contract, but rather just the inductive step, we get better results:

```smt2
(define-fun f ((x_pre Int) (y_pre Int) (z_pre Int) (scalar Int)
               (x_post Int) (y_post Int) (z_post Int)) Bool
  (and (>= scalar 1) (= x_post (* x_pre scalar)) (= z_post (* z_pre scalar)) (= y_pre y_post)))

(define-fun g ((x_pre Int) (y_pre Int) (z_pre Int) (scalar Int) (x_post Int) (y_post Int) (z_post Int)) Bool (and (>= scalar 1) (= y_post (* y_pre scalar)) (= z_post (* z_pre scalar)) (= x_pre x_post)))


(define-fun invariant ((x Int) (y Int) (z Int)) Bool (= z (* x y)))

(assert (forall ((x_pre Int) (y_pre Int) (z_pre Int) (scalar Int)
                (x_post Int) (y_post Int) (z_post Int))
             (=> (and (<= 0 x_pre)
                      (<= 0 y_pre)
                      (<= 0 z_pre)
                      (<= 0 scalar)
                      (invariant x_pre y_pre z_pre)
                      (or (f x_pre y_pre z_pre scalar x_post y_post z_post)
                          (g x_pre y_pre z_pre scalar x_post y_post z_post))
                      )
            (invariant x_post y_post z_post)
        ))
)

(check-sat)
(get-model)
```

The SMT query above asserts that for any state satisfying the invariant, applying either the method f or g the invariant will continue to hold. This theorem is provable by z3's SMT solver.

## Inductive vs. non-inductive invariants

It is worth noticing that the argument for why the invariant `x * y == z` holds true of the `Homogeneous` contract relies on the fact that the invariant is _inductive_. An inductive invariant is a property such that, asssuming the invariant holds before the execution of any method, it remains true after its execution. When an invariant is inductive, the proving heuristic is fairly straight forward: we just need to show that it is preserved by every contract method.
Notice that this is not the case for the invariant `x < 9` of the contract `C` above. Assuming `x < 9` and applying `j`, it is not the case that `x < 9`. Instead, to prove such an invariant we must first find a stronger invariant (in this case `x < 3`) which is inductive, and then demonstrate that the inductive invariant implies the original one.

## Conclusions

Combining non-linear arithmetic expressions and horn clauses to model smart contract invariants proves difficult for SMT-based approaches.
But proving only the inductive step and employing a "meta-proof" that these steps are sufficient to conclude the invariant might be a more feasible strategy for proving more complicated invariants. This strategy only works when the invariant in question is inductive, however.
