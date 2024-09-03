abstract sig Persona{}

sig Alumno extends Persona{
	libreta: one NroLibreta,
	materiasInscriptas : set Materia,
	historiaAcademica : set Materia  //conjunto de materias aprobadas
}

sig NroLibreta{}

abstract sig Docente extends Persona {
	legajo : one NroLegajo
}

sig NroLegajo{}

sig AyudanteB extends Docente {}

sig AyudanteA extends Docente {}

sig Asistente extends Docente {}

sig Profesor extends Docente {}

sig Materia {
	codigo : one CodigoMateria,
	docentes : set Docente,
	correlativas : set Materia
}

sig CodigoMateria{}


//Un ayudante B corresponde a un ayudante alumno
fact ayudanteBesAlumno {
	all p : Persona | p in AyudanteB implies p in Alumno
}

//Un alumno puede estar inscripto como maximo en 2 materias
fact maximoMaterias {
	all a : Alumno | #(a.materiasInscriptas) < 3
}

//Los alumnos no deben estar inscriptos en materias sin docentes asociados
fact materiasConDocentes {
	all a : Alumno , m : Materia | m in a.materiasInscriptas implies some m.docentes
}

////////////////////////

//Obtener el listado de docentes que dictan una materia
fun obtenerDocentes [mat: Materia] : set Docente {
	mat.docentes
}

//Obtener el listado de alumnos que cumplen con los requisitos de correlatividad para cursar
//una materia

fun alumnosCorrelatividad [mat : Materia] : set Alumno {
	{ alumno : Alumno |  mat.correlativas in alumno.historiaAcademica}
}

pred anadirDocente[d: Docente, m1,m2:Materia] {
	//El docente no tiene que estar ya asignado a la materia
		d not in m1.docentes and m2.docentes= m1.docentes+ d
	//Quedaria por chequear que si es ayudanteB, debe tener la materia aprobada
}


// Un alumno puede inscribirse en una materia
pred puedeInscribirse [a1,a2: Alumno, m: Materia] {
	a1 in alumnosCorrelatividad[m] and 
	m not in a1.materiasInscriptas and
	m not in a1.historiaAcademica and
	a2.materiasInscriptas = a1.materiasInscriptas+ m
	//Los alumnos no deberian inscribirse en mas de 2 materias ni una materia sin docente asociado
	//Esto ya se controlo con los facts
}

//Un alumno puede desincribirse en una materia
pred puedeDesinscribirse[a1,a2: Alumno, m: Materia] {
	m in a1.materiasInscriptas and 
	a2.materiasInscriptas = a1.materiasInscriptas - m
}

//Chequear si es posible agregar una materia aprobada al historial academico de un alumno
pred agregarMatAlHistorial [m: Materia, a1,a2 :Alumno] {
	puedeDesinscribirse[a1,a2,m] and m not in a1.historiaAcademica

	//Asumo que el control de si la materia fue verdaderamente aprobada queda por fuera
	//del alcance del modelo

}








run {} for 5
