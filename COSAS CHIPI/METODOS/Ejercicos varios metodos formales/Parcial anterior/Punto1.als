sig Persona { }

sig Alumno in Persona { 
       lib: lone Libreta 
}
sig Docente in Persona { 
leg: some Legajo 
}

sig ID {}

sig Codigo, Legajo, Libreta extends ID {}

sig Curso {
cod: one ID,
alumnos: some Alumno,
docentes: set Docente
}


fact { all disj c1, c2: Curso | c1.cod != c2.cod }

fact { no disj p1, p2: Persona | p1.lib = p2.lib }

fact { #(Curso.docentes) >= 1 }

fact { all c: Curso | c.alumnos != c.docentes }


//Probar que un alumno no puede tener libreta ya que usa lone(0 o 1), 
//run AlumnoSinLibreta { some p:Alumno | p.lib = none }
// Vemos en el segundo caso como se crea un alumno sin libreta


// Probando que un docente puede tener mas de un legajo
//run Docente2Legajos{some p:Docente | #(p.leg) = 2 }
//Vemos que se creo en el segundo caso una docente con dos legajos

//Quiero ver si se crea un Curso con el mismo ID
//run CursoMismoID{no disj c1,c2:Curso  | c1.cod = c2.cod }
//Que sucede, al curso tener puesto ID y no codigo, hace que su ID sea el legajo de una docente(a su vez lo comparte)


//Pruebo que no haya un docente en un curso
//run CursoSinDocente{some c:Curso | #(c.docentes) = 0 }
//me duelve una instancia sin Docente en un curso

//Probando tener asociado un Libreta a un Curso, cuando deberia de tener asociado un Codigo 		
//run CursoConLibreta{ some c:Curso | c.cod=Libreta}
// Me devuelve una instancia con un curso asociado a una libretra, lo cual esta mal, deberia retornar un codigo

//Pruebo un curso donde una persona sea alumno y docente al mismo tiempo 
//run DocenteYAlumnoEnMismoCurso{some p:Persona , c:Curso |  p in c.alumnos and p in Docente}
// termina retornando una Persona que es alumno y docente del mismo curso, lo cual es una inconsistencia






  
