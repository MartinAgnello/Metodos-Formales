public class Order {

	private /*@ spec_public @*/ Item[] Items;
	private /*@ spec_public @*/ boolean OpenOrder;
	private /*@ spec_public @*/ boolean ClosedOrder;
	
	/*@ public invariant OpenOrder <==> !ClosedOrder; @*/
	/*@ public invariant ClosedOrder <==> !OpenOrder; @*/
	// Toda orden debe estar o bien abierta o cerrada

	/*@ public invariant Items.length <=2; @*/
	// Las ordenes tienen un maximo de 2 items

	public Order (/*@ nullable @*/ Item[] OrderItems ) {
		this.Items = OrderItems;
		this.OpenOrder = true;
		this.ClosedOrder = false;
	}
	
	
	public /*@ pure @*/ boolean isOpen() {
		return OpenOrder;
	}
	
	
	/*@ public normal_behavior
	  @ requires OpenOrder == true;
	  @ ensures ClosedOrder == true && OpenOrder == false;
	  @ assignable OpenOrder,ClosedOrder;
	  @*/
	public void close() {
		if (OpenOrder) {
			OpenOrder = false;
			ClosedOrder = true;
		}
	}
	// Define el efecto de cerrar la orden	
	
	/*@ public normal_behavior
	  @ requires Items == null;
	  @ ensures \result == 0;
	  @ 
	  @ also
	  @ 
	  @ public normal_behavior
	  @ requires Items!= null; 
	  @ ensures \result < 0;
	  @*/
	public int orderValue() {
		if (Items.length == 1)
			return Items[0].getValue();
		else if (Items.length == 2 )
			return Items[0].getValue() + Items[1].getValue();
		else return 0;
	}
	// Calcula el valor de la orden, el cual se define como la suma de los valores de sus items
}
