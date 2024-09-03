public class Leg {

	/* 1. Augment the class Leg with a JML specification stating that start and end point
		are not the same. */	

	/*@ public invariant startX != endX || startY != endY; @*/
	private /* @ spec_public @ */ int startX ;
	private /* @ spec_public @ */ int startY ;
	private /* @ spec_public @ */ int endX ;
	private /* @ spec_public @ */ int endY ;

	// some methods
}
