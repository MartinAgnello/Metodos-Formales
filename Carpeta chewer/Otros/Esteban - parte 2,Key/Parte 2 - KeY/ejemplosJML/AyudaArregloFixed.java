
public class AyudaArregloFixed {

	/*@ public normal_behavior
	  @ requires (pos >= 0 && arreglo.length !=0) && (pos < arreglo.length);
	  @ requires nuevoElem >arreglo[pos];
	  @ ensures arreglo[pos] == nuevoElem;
	  @ assignable arreglo[pos];
	  @ 
	  @ also
	  @ 
	  @ public normal_behavior
	  @ requires (pos >= 0 && arreglo.length !=0) && (pos < arreglo.length);
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
