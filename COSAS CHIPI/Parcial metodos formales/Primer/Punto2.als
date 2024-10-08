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
cod: one Codigo,
alumnos: some Alumno,
docentes: set Docente
}


fact { all disj c1, c2: Curso | c1.cod != c2.cod }


fact { no disj p1, p2: Persona | p1.lib = p2.lib }


fact { #(Curso.docentes) >= 1 }


fact { all c: Curso | c.alumnos != c.docentes }




//Punto 2

// Una de las caracteristicas que deberian ser satisfechas que no se encuentra satisfecha ni en el diagrama ni en el texto 
// es que una persona podria ser alumno y  docente del mismo curso lo cual no tendria sentido, lo que si es correcto que suceda es que
// una persona pueda ser docente de un curso y alumno de OTRO curso. Otro error es que un alumno podria no tener libreta ya que 
// se uso lone y se deberia haber usado un one. 


// Hago que una persona que sea alumno de un curso no pueda ser un subconjunto de los docente de ese curso.
fact{all c:Curso | (c.alumnos ! in c.docentes )}
fact{all c:Curso | (c.docentes ! in c.alumnos )}


//buso chequear que una persona pueda ser alumno y docente pero deberan ser de cursos distintos por eso se hizo el fact anterior
run unaPersonaAlumnoYDocenteCursosDistintos{some p:Persona , c:Curso |  p in c.alumnos and p in Docente}



  
