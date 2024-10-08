sig Persona { }
//Modifique lone por one ya que podria crear una un alumnno sin libreta
sig Alumno in Persona { 
       lib: one Libreta 
}
//modifique el some por one ya que podia crear mas de un legajo para una docente
sig Docente in Persona { 
leg: one Legajo 
}

sig ID {}

sig Codigo, Legajo, Libreta extends ID { }

sig Curso {
//Modifique el ID por Codigo ya que podia un curso tener un legajo o libreta, cuando en el enunciado dice que tiene un Codigo
cod: one Codigo,
alumnos: some Alumno,
docentes: set Docente
}



fact { all disj c1, c2: Curso | c1.cod != c2.cod }

//Modifique el Persona por Alumno ya que el alumno tiene lbreta
fact { no disj p1, p2: Alumno | p1.lib = p2.lib }

//Agregue para que un docente no tenga el mismo legajo
fact{ no disj p1,p2: Docente | p1.leg = p2.leg}

fact { #(Curso.docentes) >= 1 }

fact { all c: Curso | c.alumnos != c.docentes }

//Agregado en el punto 2
fact{all c:Curso | (c.alumnos ! in c.docentes )}

fact{all c:Curso | (c.docentes ! in c.alumnos )}

