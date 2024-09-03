public class FlightRoute {

	/* . The class FlightRoute manages its legs using the array route of a fixed size.
		The integer typed attribute size points to the next free element of the array not
		yet occupied by a leg, i.e., all array components up-to but excluding size are
		non-null 
	*/

	/* (a) the attribute route is never null.  */
	//@ public invariant route!=null; */

	/* (b) the attribute size is never negative and less-or-equal than the length of the
	array route.*/
	//@ public invariant size>=0 && size<=route.length; @*/

	/*@ public instance invariant// no duplicates (c)
		@ (\forall int i;\forall int j; i>=0 && i<j && j<size;route[i]!=route[j]);

	@ 	public instance invariant// consecutive
	@ 		(\forall int i; i>=0 && i<size-1;
	@ 			route[i].endX == route[i+1].startX && route[i].endY == route[i+1].startY );
	@*/


	private /* @ spec_public @ */ int size ;
	private /* @ spec_public nullable @ */ Leg [] route ;


	/* (e) if method append is called in a state where
			• size is strictly smaller than the length of array route
			• the given parameter leg appended to the route does not violate the
		      property stated in items 2c and 2d 
		 then the method terminates normally and in its final state
			• the handed over leg has been appended to (added to the end of) the route
			and
			• the field size has been updated correctly. */

    /*@ public normal_behavior
    @ requires size < route.length;
    @ requires (\forall int i; i>=0 && i<size; route[i] != leg);
	@ requires size > 0 ==> (leg.startX == route[size - 1].endX && leg.startY == route[size - 1].endY);
    @ ensures route[\old(size)] == leg;
    @ ensures size == \old(size)+1;
    @ assignable size,route[size];
    @ */
	public void append ( Leg leg ) { 
		// ... 
	}


	/*@ public normal_behavior
		@ requires (\exists int i; i>=0 && i<size; route[i] == oldLeg);
		@ requires newLegs.length >= 1;
		@ requires size <= route.length - newLegs.length + 1;
		@ requires (\forall int i; i>=0 && i<size; (\forall int j; j>=0 && j<newLegs.length; route[i] != newLegs[j]));
		@ // The following requires clause was accepted as sufficient,
		@ // even if it does not check whether newLegs has holes already.
		@ requires size > 0 ==> ( newLegs[0].startX == oldLeg.startX && newLegs[0].startY == oldLeg.startY
		@		 && newLegs[newLegs.length - 1].endX == oldLeg.endX  && newLegs[newLegs.length - 1].endY == oldLeg.endY);
		@ // The next requires clause was not asked for; any other
		@ // solution or ignoring the issue was accepted, too. */
	public int replace ( Leg oldLeg , Leg [] newLegs ) {
		
		// ... 
	}


//OTRO REQUIRE, NO NECESARIO
/*
	@ requires
	@ (\forall inti; i>=0 && i<newLegs.length; newLegs[i] != oldLeg);
	@ ensures(\forall int i; i>=0 && i<size; route[i] != oldLeg);
	@ ensures \old(route[\result])==oldLeg;
	@ ensures(\forall int i; i>=0&&i<\result;route[i]==\old(route[i]));
	@ ensures(\forall int i; i>=\result && i< \result+newLegs.length; route[i]==newLegs[i - \result]);
	@ ensures(\forall int i; i>=\result+newLegs.length && i<size; route[i]==\old(route[i-newLegs.length+1]);
	@ ensures size == \old(size) + newLegs.length - 1;
	@ assignable size, route[*];
@*/
public int replace(Leg oldLeg, Leg[] newLegs) { ... }
// some more methods
}

	// some more methods
}