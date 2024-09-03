public class Materia {

	private int Codigo;
	private Persona[] Docentes;
	private Materia[] Correlativas;

	
	public Materia (int Cod, Materia[] Corr) {
		// Asigna el código y conjunto de correlativas de la materia
		// Inicializa los Docentes y Alumnos asociados a la materia
	}
	
	public int codigoMateria() {
		// ...
	}
	
	public Persona[] listadoDocentes() {
		// ...
	}
	
	public Materia[] listadoCorrelativas() {
		// ...
	}
	
	public void asignarDocente(Persona P) throws ExcAsignacionInvalida {
		// Si P es docente y se verifican los requisitos de asignación docente, entonces realiza el efecto de la asignación
		// Si P es docente y no se verifican los requisitos de asignación docente, entonces la operación no tiene efecto
		// Si P no es docente, lanza una excepción
	}
	
}
