class Loop2 {

    /*@public invariant 
      x>=0 && y>0 ;
  
     */ 
    public int x;
    public int y;
    
  /*@ public normal_behavior 
    @ ensures (\result * y <= x) && ((\result +1) * y > x);
    @ diverges true;
    @*/ 
    public /*@ pure @*/int method() {
	int  x1 = x, q = 0;
       /*@ loop_invariant
          @  (x1 >= 0) && ( q * y + x1 == x) ;
	  @ assignable x1,q;
	  @ decreasing x1;	
          
          @*/
       while (x1 >= y) {
                       x1 = x1 - y;
                       q = q + 1;
                       }

       return q;
    }

    // ensures (\result >=0) && (\result < y) && (\exists int k; k >=0 && k <=x; k * y + \result == x);
    //  decreasing (x1 - y);
}
