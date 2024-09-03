/**
 * Class whose objects represent the automated teller machines of our bank.
 */
public class ATM {

    /*@ accessible \inv:this.*, this.insertedCard.*; @*/

    /**
     * A bank card that is possibly inserted into the ATM at the time
     */
    /*@ public invariant insertedCard != null ==> \invariant_for(insertedCard);
      @*/
    private /*@ spec_public nullable @*/ BankCard insertedCard = null;
    /**
     * <code>true</code> iff there is a card inserted and the customer has
     * entered the right PIN
     */
    private /*@ spec_public @*/ boolean  customerAuthenticated = false;
    /**
     * Count the number of wrong PINs entered since a valid card was inserted
     */
    private /*@ spec_public @*/ int wrongPINCounter = 0;
    
    
    /**
     * Enter the PIN the belongs to the currently inserted bank card into the
     * ATM. If a wrong PIN is entered three times in a row, the card is
     * confiscated. After having entered the correct PIN, the customer is
     * regarded is authenticated
     * 
     * @param pin
     *            the PIN that is entered
     */
    /*@ public normal_behavior
        requires  insertedCard != null;
        requires  !customerAuthenticated;
        requires  !insertedCard.invalid;
        requires  pin == insertedCard.correctPIN;
        assignable customerAuthenticated;      
        ensures   customerAuthenticated;
      
        also
      
        public normal_behavior
        requires  insertedCard != null;
        requires  !customerAuthenticated;
        requires  pin != insertedCard.correctPIN;
        requires  wrongPINCounter < 2;
        assignable wrongPINCounter;
        ensures   wrongPINCounter == \old(wrongPINCounter) + 1;
        ensures   !customerAuthenticated;
      
        also
        
        public normal_behavior
        requires  insertedCard != null;
        requires  !customerAuthenticated;
        requires  pin != insertedCard.correctPIN;
        requires  wrongPINCounter >= 2;
        assignable insertedCard, wrongPINCounter, 
                   insertedCard.invalid;    
        ensures   insertedCard == null;
        ensures   \old(insertedCard).invalid;
        ensures   !customerAuthenticated;
      @*/
    public void enterPIN (int pin) {
        if ( !( cardIsInserted () && !customerIsAuthenticated () ) )
	    throw new RuntimeException ();
        if ( insertedCard.pinIsCorrect ( pin ) ) {
            customerAuthenticated = true;
        } else {
            ++wrongPINCounter;
            if ( wrongPINCounter >= 3 ) confiscateCard ();
        }
    }
    
    /**
     * @return <code>true</code> iff a card is inserted in the ATM
     */
    private /*@ pure @*/ boolean cardIsInserted () {
        return insertedCard != null;
    }

    /**
     * @return <code>true</code> iff a customer is regarded as authenticated,
     *         i.e. if a valid card is inserted and the correct PIN has be
     *         entered
     */
    private /*@ pure @*/ boolean customerIsAuthenticated () {
        return customerAuthenticated;
    }

    /**
     * Confiscate an inserted card. This invalidates the card; afterwards, the
     * card is no longer regarded as inserted
     */
    /*@
        public normal_behavior
        requires  insertedCard != null;
        ensures   insertedCard == null;
        ensures   \old(insertedCard).invalid;
        ensures   !customerAuthenticated;
        assignable insertedCard, customerAuthenticated, insertedCard.invalid;
      @*/
    public void confiscateCard () {
        if ( !cardIsInserted() ) throw new RuntimeException ();
        insertedCard.makeCardInvalid ();
        insertedCard = null;
        customerAuthenticated = false;        
    }
    
}
