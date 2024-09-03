public class ArrayHelper {

    /*@ public normal_behavior
      @ requires at >= 0 && at < array.length;
      @ {|
      @ requires newE > array[at];
      @ ensures array[at] == newE;
      @
      @ also
      @
      @ requires newE <= array[at];
      @ ensures true;
      @ assignable \nothing;
      @ |}
      @*/
    public static void replaceIfGreater(int newE, int at, int[] array) {
	if (newE > array[at]) {
	    array[at] = newE;
	}
    }


}