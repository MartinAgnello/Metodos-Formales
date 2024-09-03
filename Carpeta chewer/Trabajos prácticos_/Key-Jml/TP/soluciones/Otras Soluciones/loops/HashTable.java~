
public class HashTable {
    
	// Open addressing Hashtable with linear probing as collision resolution.

	/*@ public invariant 
	  @ h.length == capacity;
	  @*/
	
	/*@ public invariant 
	  @ size >= 0 && size <= capacity;
	  @*/	
	public /*@ spec_public @*/ int size; 
	
	/*@ public invariant 
	  @ capacity >= 1;
	  @*/	
	public /*@ spec_public @*/ int capacity;

	/*@ public invariant 
	  @ h != null;
	  @*/
	
	/*@ public invariant 
	  @ \typeof(h) == \type(Object[]); 
	  @*/	 
	public /*@ spec_public nullable @*/ Object[] h;

		
	HashTable (int capacity) {
		h = new Object[capacity]; 
		this.capacity = capacity;
		size = 0;
	}
	
	/*@ public normal_behavior
	  @ requires val >= 0; 
	  @ ensures \result >= 0 && \result < capacity;
	  @*/	
	public /*@ pure @*/ int hash_function (int val) {
        int result = 0;
        
		if (val >= 0) {
		   result = val % capacity;			
                   return result;
                }
	}
		
	// Add an element to the hashtable.
	/*@ public normal_behavior
	  @ requires size < capacity && key >= 0; 
	  @ ensures size == \old(size)+1;
	  @ ensures (\exists int i; i>= 0 && i < capacity; h[i] == u &&
	            (\forall int j; j >= 0 && j < capacity && j != i; h[j] == \old(h[j])));	  
	  @ assignable size, h[*];
	  @
	  @ also
	  @
	  @ public normal_behavior
	  @ requires size >= capacity;
	  @ ensures (\forall int j; j >= 0 && j < capacity; h[j] == \old(h[j]));
          @ assignable \nothing;
	  @	  
	  @*/
	public void add (Object u, int key) {

	    if (size < capacity) {
    
	    int i = hash_function(key);

		if (h[i] == null) {
		    h[i] = u;
			size++;
			return;
			}
		else {		
			int j = 0;
	        /*@ loop_invariant j >= 0 && j <= capacity && i >= 0 && i < capacity;
		      @ assignable j,i;
		      @ decreases capacity - j;
		      @*/
			while (h[i] != null && j < capacity)
		    {
             if (i == capacity-1) i = 0;
             else {i++;}
             
             j++;
		    }
			
			h[i] = u;
			size++;
			return;			
		  }	

        } else {
               return;
               }	
	}   
	
}
