public class Person {    

    private /*@ spec_public @*/ String name;

    /*@ public invariant age >= 0; @*/
    private /*@ spec_public @*/ int age;
   
    /*@ public invariant license.active ==> age >= 18; @*/
    //@ public invariant (\forall Person p;p.license == this.license; p == this);
    private /*@ spec_public @*/ DriverLicense license;

        
    public Person(String name, int age, DriverLicense license) {
	this.name    = name;
	this.age     = age;
	this.license = license;
    }

    
    /*@ public normal_behaviour 
      @ requires true;
      @ ensures \result == license.active();
      @*/
    public /*@ pure @*/ boolean canDrive() {
	return license.active();
    }

    /*@ public normal_behaviour
      @ ensures age == \old(age) + 1;
      @ assignable age;
      @*/
    public void birthday() {
	age++;
    }

    /*@ public normal_behaviour 
      @ requires age>=18;
      @ ensures license.active;
      @
      @ also
      @
      //focus on verifying only the class invariants 
      @ requires true;
      @ ensures true;
      @ 
      @ also
      @ public exceptional_behaviour
      @ requires age < 18;
      @ signals (NotOldEnoughException) true;
	  @ assignable \nothing;
      @*/     
    public void activateLicense() throws NotOldEnoughException {
	if (age < 18) {
	    throw new NotOldEnoughException();
	} 
	license.setActive(true);
    }

}
