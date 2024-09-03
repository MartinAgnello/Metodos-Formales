class Loop1 {

    /*@ public invariant 
      @  x > 0 ;
      @*/ 
    public int x;

    
  /*@ public normal_behavior 
    @ requires true;
    @ ensures \result == x * x;
    @ diverges true;
    @*/ 
    public /*@ pure @*/int method() {
      int  y = x;
      int  z = 0;
       /*@ loop_invariant
          @  (y >= 0) && ( x * y + z == x * x) ;
	  @ assignable y, z;
          @ decreasing y ;
          @*/
	
       while (y > 0) {
                      z = z + x;
                      y = y - 1;
                      }
 
       return z;
    }
}
