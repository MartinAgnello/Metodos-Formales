public classInterval {


	/*Augment class Interval with JML specification stating that getEnd() is always ≥ getStart(). @*/

	/*@ public invariant getEnd() >= getStart() @*/
	
	private /*@ spec_public @*/ final int start, end;

	public Interval(int start, int end) {
		this.start = start;
		this.end = end;
	}

	public /*@ pure @*/ int getStart() {
		return start;
	}
	public /*@ pure @*/ int getEnd() {
		return end;
	}
}
