
public class ColaDeEspera {
Object [] arreglo;
int largo;
int primero;
int proximo;

/*@ public invariant
  @ (primero >=0 ) && (primero < proximo) && (proximo < largo);
  @*/
ColaDeEspera (int tope){
	//to do
}

public int largo(){
	return this.largo;
}

public void agregarElemento (Object x){
	// ...
}

public Object sacarElemento(){
	if (this.largo > 0){
		if(arreglo[primero]!=null){
			Object x = arreglo[primero];
			for(int i=primero; i< proximo; i++){
				arreglo[i] = arreglo[i+1];
			}
			proximo = proximo - 1; 
		    // Aca va el codigo para correr los elementos del arreglo un lugar
			return x;		
		}
		else return null;
		
	}
	else return null;
}
}
