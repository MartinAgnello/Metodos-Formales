public classHashtable {

	//The size field is never negative, and always ≤ capacity.
	/*@ public invariant size>=0 && size <= capacity; @*/

	//There should be space for at least one element in the hash table.
    /*@ public invariant capacity > 0; @*/

	//The capacity should be the same value as h.length.
	/*@ public invariant capacity==h.length; @*/

	//The array h cannot be null
	/*@ public invariant h != null; @*/  

	/* The number of elements stored in array h (i.e., the number of array cells whose
    content is not null) is size. */
	/*@ public invariant (\sum int i; 0 <= i && i < capacity && h[i] != null; 1) == size; @*/


	private /*@ spec_public nullable @*/ Object[] h;
	private /*@ spec_public @*/ int capacity;
	private /*@ spec_public @*/ int size = 0;

	// Specifying the constructor was not required
		/*@ public normal_behaviour
		@ ensures this.capacity == capacity;
		@ ensures size == 0;
		@ assignable h[*], capacity, size;
		@*/

	Hashtable (int capacity) {
		h = newObject[capacity];
		this.capacity = capacity;
	}

	/*@ public normal_behavior
	@ requires val > 0;
	@ ensures \result>= 0 && \result=< capacity;
	@*/
	private /*@ pure  @*/ int hash_function (int val) {
		// ..... 
	}


	/* • If the size is strictly smaller than capacity, then all of the following must hold:
			– add terminates normally
			– add increases size by one
			– After add(obj,key), the object obj is stored in h at some index i.
	   • If the size has reached capacity, add will throw an FullHashtableExcept */

	 /*@ 
	 @ public normal_behavior
	 @ requires size < capacity && key>0;
	 @ ensures \size == \old(size)+1;
	 @ ensures (\exists int i; i>=0 && i< capacity; h[i]==obj);
	 @ assignable h[*], size;
	 @
	 @ also
	 @
	 @ public exceptional_behavior
	 @ requires size >= capacity && key>0;
	 @ signals_only FullHashtableExcept;
	 @ assignable \nothing;
	 @*/

	public void add (Object obj, int key) {
		if(size < capacity) {
			int i = hash_function(key);
			if(h[i] == null) {
				h[i] = obj;
				size++;
			}
			else{
				while(h[i] != null){
					if(i == capacity-1) {
						i = 0;
					} else {
						i++;
					}
				}
				h[i] = obj;
				size++;
			}
			return;
		} else {
			throw newFullHashtableException();
		}
	}


}