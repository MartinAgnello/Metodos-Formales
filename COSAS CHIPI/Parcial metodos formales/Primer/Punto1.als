sig Persona { }

// lone permite que tenga 1 o 0 libreta y en el digrama marca 1.
sig Alumno in Persona { 
       lib: lone Libreta 
}

// Docente permite que tenga 1 o mas Legajos y en el diagrama marca 1
sig Docente in Persona { 
leg: some Legajo 
}

sig ID {}

sig Codigo, Legajo, Libreta extends ID {}

// el curso permite que el codigo sea un ID y NO un codigo, en el diagrama marca que tiene un Codigo
sig Curso {
cod: one ID,
alumnos: some Alumno,
docentes: set Docente
}


fact { all disj c1, c2: Curso | c1.cod != c2.cod }

fact { no disj p1, p2: Persona | p1.lib = p2.lib }

fact { #(Curso.docentes) >= 1 }

fact { all c: Curso | c.alumnos != c.docentes }


// Existencia de atomos de todas las signaturas, esta bien asi? basicamente tendria 
// que crear un atomo de cada uno de las signaturas
run TodasLasAsignaturas {some c:Curso | #(c.alumnos)>1 and  #(c.docentes)>1 }


//Existencia de tuplas de todas las relaciones
// Seria Persona con libreta, Docente con legajo, Curso con Id Alumni y Docente, eso seria??
run AlumnoConLibreta {some a:Alumno | #a.lib = 1}


// Existencia de persona sin Libreta y sin leg
// no puedo hacer de personas por eso separo Docente y alumno
// No devuelte instasncia por ende esta bien abarcado lo que se solicito
run DocenteSinLegajo { one d:Docente | #(d.leg)=0 } 
// devuelve un alumno sin libreta lo cual no deberia de pasar
run AlumnoSinLibreta { one a:Alumno | #(a.lib)=0 and (a !in Docente) } 

// Como lo hago?
run PersonaAlumnoYDocenteConIDyLegajo{ one p:Persona | (p in Alumno) and (p in Docente) }


//* Todo ID es Código, Libreta o Legajo (ID "abstracta"): No
// Seria que un ID sin ser Codigo, Legajo y Libreta. ESTA BIEN??
run IDNoCodigoLibretaLegajo { one id:ID | (id !in Codigo) and (id !in Libreta) and (id !in Legajo) }

// Pruebo si puede haber un legajo,Libreta y Codigo sin ser ID, no devuelve ninguna instancia
// por lo tanto esta bien validado.
run CodigoLibretaLegajoNoID { some c:Codigo, l:Libreta, le:Legajo | (c !in ID ) or (l !in ID) or (le !in ID ) }

// El código de un curso es efectivamente un Código (con esto esta bien? )
run CursoConIDNoCodigo { some c:Curso | c.cod !in Codigo }

// El legajo de un docente es efectivamente un Legajo:
// No devuelve instancia, o sea esta ok 
run DocenteLegajoNoSeaLegajo {some d:Docente | d.leg !in Legajo}

// Los docentes de un curso son Docentes: No. ESTO SERIA???
run DocentesNoDocentes {some c:Curso | c.docentes !in Docente}

// Los alumnos de un curso son Alumnos: No
run AlumnosNoAlumnos {some c:Curso | c.alumnos !in Alumno}

//Una persona puede ser docente o alumna en cursos dictados por la institución. ESTO SERIA?
run PersonaDocenteYAlumno { one p:Persona | (p in Docente) and (p in Alumno) }


//Un código, ni más ni menos en un Curso
// no devuelve nada, ya que estoy pidiendo que me de un curso con la cant de codigo distinto de 1 
run CursoConMasdeUnCodigo { some c:Curso | #c.cod!=1 }


//No hay dos cursos distintos con el mismo código
// porque me devuelve esto? que hace en base a lo que puse?
run DosCursosMismoCodigo {some c1,c2: Curso | c1.cod = c2.cod}
// bien hecho
run DosCursosMismoCodigoBien {some c1,c2: Curso | c1.cod = c2.cod and (c1 !in c2)}

//Cada curso posee al menos un docente encargado de su dictado
// retorna un Curso sin Docente lo cual no puede pasar
run CursoSinDocente {some c:Curso | #c.docentes=0}

// Cada curso posee un conjunto de alumnos inscriptos al mismo??????????????????? que no sea vacio


// No hay dos docentes distintos con el mismo legajo
// Retorna dos Docente con el mismo legajo, lo cual esta mal
run DosDocenteMismoLegajo {some d1,d2:Docente | (d1.leg = d2.leg) }

// La cantidad de docentes de cada curso no puede superar a la cantidad de alumnos del mismo:
// Retorna 
run MasDocentesQueAlumnos {some c:Curso | #(c.docentes) > #(c.alumnos)}





























  
