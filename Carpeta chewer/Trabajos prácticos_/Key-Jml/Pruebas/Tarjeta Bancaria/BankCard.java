/**
 * Class for representing bank cards. The class provides attributes for the PIN
 * of the card (abstracting from any kind of more advanced PIN storage concept)
 * and the account number. Cards can be invalidated by ATMs (used when cards are
 * confiscated), which is simulated using a boolean attribute.
 */
public class BankCard {

    /*@ accessible \inv:this.*; @*/

    /**
     * The correct PIN that needs to be entered when using <code>this</code>
     * card
     */
    private /*@ spec_public @*/ final int correctPIN;
    
    /**
     * This attribute is <code>true</code> iff the card represented by this
     * object has been deactivated
     */
    private /*@ spec_public @*/ boolean invalid = false;
    
    public /*@ pure @*/ BankCard (final int correctPIN) {
        this.correctPIN = correctPIN;
    }
    
    /**
     * Determine whether a given PIN is correct for this card. For invalid
     * cards, this check always returns <code>false</code>
     * 
     * @param pin
     *            the PIN that is supposed to be checked
     * @return <code>true</code> iff <code>pin</code> is correct and the
     *         card is valid
     */
    /*@
        public normal_behavior
        ensures  \result <==> (!invalid && pin == correctPIN);
      @*/
    public /*@ pure @*/ boolean pinIsCorrect (int pin) {
        if ( cardIsInvalid () ) return false;
        return correctPIN == pin;
    }
    
    /**
     * @return <code>true</code> iff <code>this</code> card is invalid
     */
    /*@
        public normal_behavior
        ensures  \result == invalid;
      @*/
    public /*@ pure @*/ boolean cardIsInvalid () {
        return invalid;
    }    

    /**
     * Invalidate a card
     */
    /*@
        public normal_behavior
        ensures  invalid;
        assignable invalid;
      @*/
    public void makeCardInvalid () {
        invalid = true;
    }
   
}
