
public class AyudaArreglo {

	/*@ public normal_behavior
	  @ requires nuevoElem >arreglo[pos];
	  @ ensures arreglo[pos] == nuevoElem;
	  @ 
	  @ also
	  @ 
	  @ public normal_behavior
	  @ requires nuevoElem <= arreglo[pos];
	  @ ensures true;
	  @ assignable \nothing;
	  @*/
	
	public static void reemplazarSiMayor (int nuevoElem, int pos, int[] arreglo){
		
		if (nuevoElem > arreglo[pos]){
			arreglo[pos] = nuevoElem;
		}
	}
}
