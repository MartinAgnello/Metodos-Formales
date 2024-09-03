public class Laberinto { 

	// CONSTANTES DE MOVIMIENTO 
	public final static int MOVER_ARRIBA = 0; 
	public final static int MOVER_ABAJO = 1; 
	public final static int MOVER_IZQ = 2; 
	public final static int MOVER_DER = 3; 

	// CONSTANTES DE CELDA 
	public final static int LIBRE = 0; 
	public final static int PARED = 1; 
	public final static int SALIDA = 2; 
	/* CAMPO DE JUEGO: 
	El campo de juego esta dado por un rectángulo donde las paredes se
	representan mediante entradas con valor Laberinto.PARED (’1’), la
	salida (de la cual hay una sola) es una entrada con valor Laberinto.SALIDA
	(’2’) y todas las demás tienen valor Laberinto.LIBRE
	(’0’).

	El primer valor determina la fila y el segundo la columna (comenzando
	desde cero).

	*/ 

	//INVARIANTES DE CLASE

	// a) El	laberinto	no	es	null;	es	decir,	el	campo	de	juego	en	sí	y	sus	componentes	no	son	null.
	/*@ 
      	public invariant 
      		(\forall int fila; fila >= 0 && fila < lab.length;
           		(\forall int col; col >= 0 && col < lab[fila].length;
                   lab[fila][col] >= LIBRE && lab[fila][col] <= SALIDA));
     @*/      
	

	// b) Cada fila del	laberinto tiene	la	misma	cantidad de	columnas.
	/*@ 
		public invariant
			(\exists int nroCol;nroCol>=0; (\forall int nroFila;nroFila>=0 && nroFila<lab.length; lab[nroFila].length= nroCol));
	@*/

	


	// d)	Cada	celda	del	laberinto	es	o	bien	una	pared,	la	salida,	o	está	libre.





	
	private int[][] lab; 

	/*  
	Posicion del jugador: 
	La posicion del jugador debera siempre estar dentro del laberinto,
	y no puede haber una pared en esa misma posicion. 
	*/ 
	// c) La	posición	ocupada	por	el	jugador	no	es	una	pared.
	/*@
		public invariant
			jugadorFila>=0 && jugadorFila < lab.length && jugadorColumna >=0 && jugadorColumna < lab[jugadorFila].length
			&& lab[jugadorFila][jugadorColumna] != PARED;

	@*/
	private /*@ spec_public @*/ int jugadorFila;
	private /*@ spec_public @*/ int jugadorColumna; 

	public Laberinto(int[][] lab, int filaComienzo, int columnaComienzo) { 
			this.lab = lab; 
		// Poner al jugador en la posicion de comienzo 
			this.jugadorFila = filaComienzo; 
			this.jugadorColumna = columnaComienzo; 
		
	} 

	/*Devuelve verdadero si el jugador ha llegado a la salida. */ 
	public boolean gano() { 
		// AUN NO IMPLEMENTADO... 
	} 

	/* 
	Un movimiento a la posicion (nuevaFila,nuevaColumna) es posible si
	y solo si la celda esta dentro del laberinto y esta libre.  
	*/ 
	public boolean esPosible(int nuevaFila, int nuevaColumna) { 
		// AUN NO IMPLEMENTADO... 
	} 

	/* 
	Toma una direccion y ejecuta el movimiento si es posible. Sino, el
	jugador permanence en la misma posicion. La direccion debe ser una
	de las definidas por las constantes MOVER_X. El valor devuelto indica si el movimiento tuvo exito. 
	*/ 
	public boolean mover(int direccion) { 
		// AUN NO IMPLEMENTADO... 

	} 

}