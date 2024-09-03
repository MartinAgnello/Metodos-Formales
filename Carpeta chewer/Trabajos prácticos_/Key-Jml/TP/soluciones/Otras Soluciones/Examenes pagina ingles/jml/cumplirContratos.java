public int x, y;
	/*@ public normal_behavior
	@ requires x>=0 && y>=0;
	@ ensures \result == (x>=y ? x : y);
	@*/

public int m() { // ... }

/*“(x>=y ? x : y)” is a conditional expression, returning x if x>=y, and y otherwise. */

/*
(a) [5p]
Which of the following four implementations of m() respect the contract? Justify
your answer in each case. You don’t need to give a formal correctness
proof. You can assume that the integers are unbound and no overflow occurs.

public int m () { // Implementation I1
	if ( y >= 0) {
		if ( x >= y ) { 
			return x ;
		} else { return y ; }
	} else 
		return 0;
}

public int m () { // Implementation I2
	x = x - y ;
	if ( x >= 0) {
	 	return x + y ;
	} else {
	 	return y ; 
	}
}

public int m () { // Implementation I3
	int t = x - y ;
	if ( t >= 0) 
	    return t + y ;
	} else { 
		return y ; 
	}
}

public int m () { // Implementation I4
	if ( x >= y ) { 
		return x ;
	} else {
		if ( y >= 0) {
		 	return y ;
		} else {
		 	return x ++; }
	}
}

(b) [3p]
Choose one of the implementations of m() that does not respect its contract,
and suggest a patch of the contract such that the (unchanged) implementation
respects that contract.


Solution
(a)
I1: Returns the correct result for a weaker precondition than required which is fine.
Contract is fulfilled
I2: The method changes x and, since the postcondition doesn’t use \old, this can lead
to a wrong result. For example, if initially x=3 and y=2 then x is changed to 1. With
that, the specified result is (1>=2 ? 1 : 2), which is 2. But the implementation
returns 3.
I3: Looks similar as I2, but does not suffer from the same problem, as no field is overwritten.
Contract is fulfilled
I4: Like in I2, the field x is changed, but only when the requires clause is not satisfied.
This is no harm, and the contract holds.
(b) The only implementation that violates the contract is I2. One easy way to patch the
contract is to enclose the conditional in the ensures clause with \old. In this case, the
side effect on x is not carried into the contract. 

*/