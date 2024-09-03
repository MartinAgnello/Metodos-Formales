public class Book {
	//1. No two books have the same ISBN
	/*@ public static invariant !(\exists Book b1,b2; b1.isbn == b2.isbn); @*/  //fijarse que se usa static

	//otra forma

	/*@ public static invariant (\forall Book b1, b2; b1 != b2 ==> b1.isbn != b2.isbn); @*/ //fijarse que se usa static
	private /*spec_public*/ int isbn;

 
	//2. A book has at least one page.
	/*3. Pages are numbered from 1 to the last page, and the current page must be within
		this range */
	/*@ public invariant currentPage > 0 && lastPage >= currentPage; @*/
	private /*spec_public*/ int currentPage;


	/*4. The bookmarks are initialized to the value 0, and can be assigned to valid page
	numbers */
	/*5. There is no duplicate in bookmarks (i.e., no two assigned bookmarks point to the
	same page) */

	/*@ public invariant (\forall int i;0 <= i && i < bookmarks.length; bookmarks[i] >= 0 && bookmarks[i] <= lastPage); @*/

	/*@ public invariant (\forall int i,j; 0 <= i && i < bookmarks.length && 0 <= j && j < bookmarks.length;
							@ i != j ==> (bookmarks[i] != bookmarks[j] || bookmarks[i] == 0)); 
	 @*/

	private /*@ spec_public @*/ int[] bookmarks = new int[10];

	private /*@ spec_public @*/ int lastPage;


	public Book (int numberOfPages, int isbn) {
		//...
	}

	/*6. A reader can try to flip a page (i.e., flip) to move to the next page. If he/she
		is already at the last page, flipping throws a BookException, and keeps the book
		(i.e., ISBN and number of pages) and the current reading state (i.e., current page
		and all bookmarks) unchanged  */

	/*@ public normal_behavior
	@	requires currentPage < lastPage;
	@	ensures currentPage == \old(currentPage)+1;
	@   assignable currentPage;
	@ 
	@	also
	@
	@	public exceptional_behavior
	@	requires currentPage == lastPage;
	@	signals_only BookException;
	@	assignable \nothing;
	@*/
	public void flip() {
		//...
	}


	/*7. A reader can jump directly to a marked page (i.e., jump) by providing the array
		index of the bookmark */

	/*@ public normal_behavior 
	@ requires index>= 0 && index < bookmarks.length;  
	@ requires bookmarks[index] != 0;
	@ ensures currentPage == bookmarks[index];
	@ assignable currentPage;
	@*/

	public void jump(int index) {
		//...
	}

	/*A reader can mark the current page (i.e., mark) by storing the page number in the
		bookmark array, without changing existing bookmarks other than the location
		that is used for the new one. (Hint: We do not care about which array location
		is used for the new bookmark.) */
	
	
	/*@ public normal_behavior
		@ ensures (\exists int i; 0 <= i && i < bookmarks.length; bookmarks[i] == currentPage);
		@ ensures (\forall int i; 0 <= i && i < bookmarks.length; bookmarks[i] == currentPage || bookmarks[i]==\old(bookmarks[i]));
		@ assignable bookmarks[*];
	@*/
	
	public void mark() {
		//...
	}
}
