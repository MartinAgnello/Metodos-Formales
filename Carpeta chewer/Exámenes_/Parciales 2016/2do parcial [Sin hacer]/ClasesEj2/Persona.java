public class Persona {

	private boolean Alumno;
	private boolean Docente;

	// Atributos de Alumno
	private int LU;
	private Materia[] HistoriaAcademica;
	private Materia[] Inscripciones;

	// Atributos de Docente
	private int Legajo;
	private int Categoria;
	/* 
	   Asociacion de Categorias Docentes: 
	   0 = AyudanteB
	   1 = AyudanteA
	   2 = Asistente
	   3 = Profesor 
	*/
	
	
	public Persona (boolean Al, boolean Doc, int numLU, int numLeg, int CatDoc) {
		// Inicializa las caracterisiticas de la persona, dependiendo de si es alumno y/o docente
		// Si es alumno, asigna LU e inicializa las estructuras correspondientes a HistoriaAcademica e Inscripciones
		// Si es docente, asigna Legajo y Categoría
	}
	
	
	public boolean esAlumno () {
		//...
	}
	
	public boolean esDocente() {	
		//...
	}
	
	public int categoriaDocente() {
		//...
	}
	
	public Materia[] historialAcademico() {
		//...
	}
	
	public Materia[] inscripciones() {
		//...
	}
	
	public void inscribirseEnMateria(Materia M) {
		// ...
	}

	public void desinscribirseDeMateria(Materia M) {
		// ...
	}
	
	public void expandirHistorialAcademico(Materia M) {
		// El efecto se produce si (entre otras cosas) se verifica que el alumno 
		// cumple los requisitos de correlatividad de la materia M
	}
	
}
