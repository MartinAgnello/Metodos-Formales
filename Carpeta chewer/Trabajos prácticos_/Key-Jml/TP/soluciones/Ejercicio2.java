
public class Ejercicio2 {

    private /*@ spec_public @*/ int[] b,c;
    private /*@ spec_public @*/ int j,k,n;
	
	
	// PRELIMINARIES (Question 2.0 ;-)
    //@ public invariant n == b.length && 0<=j && j<k && k < n;
	
	
    //The answers to the questions cannot be invariants simultaneoulsly.
    //We write them as invariants only to make them chackable by the jml checker.

    // Question 2a 
    // All elements in b[j..k] are zero.
    //@ public invariant (\forall int i; i>=j && i<=k; b[i]==0);

	// Question 2b V V                     
	// All zeros of b[0..n-1] are in b[j..k].
	//@ public invariant (\forall int i; i>=0 && i<n; (b[i] == 0 ==> i >= j && i <= k));
	

	// Question 2c
	// It is not the case that all zeros of b[0..n-1] are in b[j..k]
    // alternative 1 using negation:	
	//@ public invariant !(\forall int i; i>=0 && i<n; (b[i] == 0 ==> i >= j && i <= k));
    // alternative 2 without negation:	
	//@ public invariant (\exists int i; i>=0 && i<n; (b[i] == 0 && (i < j || i > k)));

 
    // Question 2d:
    // b[0..n-1] contains two zeros.

      /*@ public invariant \exists int i1, i2;i1>=0 && i1<i2 && i2<n;b[i1]==0 && b[i2]==0; !\exists int j ; b[j]==0 && j!=i2 && j=!i1; 
    //@ public invariant (\exists int i1,i2; i1 >= 0 && i1 < i2 && i2 < b.length; b[i1] == 0 && b[i2] == 0 && (\forall int k; 0 <=k && k<n && k!=i1 && k!=i2; b[k]!=0));
    //@ public invariant (\sum int i; i<=n-1 && i>=0 && b[i] == 0; 1) == 2;


    // Question 2e:
    // b[0..n-1] contains at least two zeros.

    //@ public invariant (\exists int i1,i2; i1 >= 0 && i1 < i2 && i2 < b.length; b[i1] == 0 && b[i2] == 0);


    // Question 2f:
    // b[0..n-1] contains at most two zeros.

    /*@ public invariant (\forall int i1,i2,i3; 0 <= i1 && i1 < i2 && i2 < i3 && i3 < b.length ;
      @                                  b[i1] != 0 || b[i2] != 0 || b[i3] != 0);
      @*/


    // Question 2g:
    // Reverse the order of elements in a.

    /*@ public normal_behavior
      @ ensures (\forall int i; i >= 0 && i < a.length; a[i] == \old(a[a.length - 1 - i]));
      @ assignable a[*];
      @*/
    public static void reverse(int[] a) {
	// ...
    }

	
    // extra Question: // not on website
    // The sum of all positive elements in a.

    /*@ public normal_behavior
      @ ensures \result == (\sum int i; i >= 0 && i < a.length && a[i] >= 0 ; a[i]);
      @*/
    public /*@ pure @*/static int sum(int[] a) {
	return 0; // stub
	// ...
    }

}
