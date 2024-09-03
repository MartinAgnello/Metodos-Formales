public class EntryList {

    /*@ spec_public @*/ Object first;

    /*@ spec_public nullable @*/ EntryList rest;
    
    EntryList( Object first, EntryList rest ) {
    	this.first = first;
    	this.rest = rest;
    }
    
    // some methods, among them:


    /*@ public normal_behavior
      @ requires rest == null;
      @ ensures \result == 1;
      @
      @ also
      @
      @ public normal_behavior
      @ requires rest != null;
      @ ensures \result == 1 + rest.size();
      @*/
    /*@ spec_public pure @*/ int size() {
	return 0; // stub
	// ...
    }
}