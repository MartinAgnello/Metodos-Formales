/*
* Class to represent sequence of intervals.
*/
public class IntervalSeq {
	//The size field is never negative, and always ≤ contents.length.

	/*@ public invariant size>=0 && size<= contents.length; */
	protected /*@ spec_public @*/ int size = 0;

	// The contents of the array which are stored below index size are never null.
	/*@ public invariant (\forall int i;i>=0 && i<size; contents[i] != null); */
	
	protected /*@ nullable spec_public @*/ Interval[] contents = newInterval[1000];
	
	/**
	* Insert a new element in the sequence;
	* it is not specified in which place
	* the element will be inserted
	*/

	/* If the size is strictly smaller than contents.length, then all of the following must hold:
			– insert terminates normally
			– insert increases size by one
			– After insert(iv), the interval iv is stored in contents at some index i below size.
					 Below index i, the array contents is unchanged. The elements stored in between i and size
					 were shifted one index upwards (as compared to the old contents).
	   If the size has reached contents.length, insert will throw an IndexOutOfBoundsException */

	/*@ public normal_behavior
	@ requires size < contents.length;
	@ ensures size = \old(size)+1;
	@ ensures(\exists int i; 0 <= i && i < size; contents[i] == iv && 
				(\forall int j; 0 <= j && j < i; contents[j] == \old(contents[j])) && 
				(\forall int k; i < k && k < size; contents[k] == \old(contents[k-1])));
	@ assignable size,contents[*],contents;
	@
	@ also
	@ 
	@ public exceptional_behavior
	@ requires size == contents.length; 
	@ signals_only IndexOutOfBoundsException;
	@ assignable \nothing;
	@ */  
	public void insert(Interval iv) {
		// ...
	}
	// more methods
}