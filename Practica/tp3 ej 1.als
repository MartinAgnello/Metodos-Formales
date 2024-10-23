sig Colegio { miembros: some Persona,
	titulares: some Persona,
	suplentes: set Persona,
	id: one ID
}

sig Provincial, Nacional extends Colegio {}

sig ID {}

sig Persona { 
	dni: one DNI,
	matricula: lone Matricula
}

sig Contador, Abogado, Farmaceutico extends Persona { }

sig DNI { }

abstract sig Matricula { }

sig MatriculaC, MatriculaA, MatriculaF extends Matricula { }
---------------------------------------------------------------
/*Factos*/
fact {all disj p1, p2: Persona | p1.dni != p2.dni}

fact {no disj p1, p2: Persona | (some p1.matricula) and (some p2.matricula) and
(p1.matricula = p2.matricula)}

fact {all disj c1, c2: Colegio | c1.id != c2.id}

fact {Colegio = (Provincial+Nacional)}

/*Ningun consejero de un Colegio puede ser titular y suplente a la vez.*/
fact {all c: Colegio | no (c.titulares & c.suplentes)}

fact {all c: Colegio | (c.titulares + c.suplentes) in c.miembros}

fact {all p: Persona | (some (MatriculaC & p.matricula)) implies (p in Contador)}

fact {all p: Persona | (some (MatriculaA & p.matricula)) implies (p in Abogado)}

fact {all p: Persona | (some (MatriculaF & p.matricula)) implies (p in Farmaceutico)}

fact {all p1, p2: Persona, c: Colegio | ((p1 in c.miembros) and (p2 in c.miembros))
	implies (mismaProfesion[p1,p2] and
	matriculadosParaMismaProfesion[p1,p2])}

fact {all c: Provincial | (#c.titulares =< 3) and (#c.suplentes =< #c.titulares)}

fact {all c: Nacional | (#c.titulares < 5) and (#c.suplentes =< 2)}
-------------------------------------------------------------
/*Predicados*/
pred mismaProfesion[p1, p2: Persona]
	{ (p1+p2 in Contador) or (p1+p2 in Abogado) or (p1+p2 in Farmaceutico) }

pred matriculadosParaMismaProfesion[p1, p2: Persona] {
	((some (p1.matricula & MatriculaC)) and (some (p2.matricula & MatriculaC))) or
	((some (p1.matricula & MatriculaA)) and (some (p2.matricula & MatriculaA))) or
	((some (p1.matricula & MatriculaF)) and (some (p2.matricula & MatriculaF)))
}

/*anadir una persona al conjunto de miembros de un colegio provincial de contadores.
Esta accion es posible siempre y cuando la persona pertenezca al consejo directivo de un colegio nacional para esa profesion*/

pred agregarMiembro[c1, c2: Colegio, p: Persona] {
	(no c3: Nacional | (p in c3.(titulares+suplentes))) and
	(p in c2.miembros) and
	(c1.titulares in c2.titulares) and
	(c1.suplentes in c2.suplentes)
}

--Nueva Version:
pred agregarMiembroV2[c1, c2: Colegio, p: Persona] {
	--Precondiciones:
	--Ambos colegios son para contadores
	(c1.titulares in Contador) and (c2.titulares in Contador) and
	--Ambos deben ser provinciales
	(c1 in Provincial) and (c2 in Provincial) and
	--La persona debe ser contador
	(p in Contador)
	--La persona pertenece a un consejo directivo de un colegio nacional
	(some c3: Nacional | (p in c3.(titulares+suplentes))) and
	--La persona no esta en c2 
	(p !in c2.titulares) and

	--Postcondiciones:
	--Agrego a p al conjunto de miembros de c2, luego los miembros de c1 y c2 deberian ser los mismos + p añadido a c2
	(p in c2.miembros) and
	(c1.miembros = c2.miembros + p)
}



---------------------------------------------------------------
/*Caso de no exito:
La persona pertenece al consejo directivo de un colegio nacional y se quiere añadir a esta persona al conj de miembros de 1 
colegio provincial de contadores, tendria que generarse una instancia pero no lo hace*/
run PersonaPerteneceNacional {some c1,c2: Colegio ,c3: Nacional, p : Persona | (p in c3.titulares) and agregarMiembro[c1,c2,p] }

/*Caso de exito:
El colegio al que se desea añadir al miembro nuevo tendria que ser provincial, pero me permite añadirlo a un colegio nacional*/
run ColegioNoProvincial {some c1,c2: Nacional, p : Persona | agregarMiembro[c1,c2,p]}

/*Caso de exito:
No se chequea que el miembro ya pertenezca al colegio que se desea añadir, al añadirlo no me tendria que generar una instancia
pero si lo hace*/
run MiembroExistente {some c1,c2 : Colegio, p: Persona | (p in c2.titulares) and agregarMiembro[c1,c2,p]}

/*Caso de exito:
No se chequea que el colegio sea de contadores, al añadir al miembro no me tendria que generar instancia pero lo hace*/
run C2NoEsColegioDeContadores {some c1,c2 : Colegio, p : Persona | #(c2.titulares.matricula & MatriculaC) = 0 and agregarMiembro[c1,c2,p]}

/*Caso de exito:
No se chequea que el miembro a añadir sea contador, al añadir al miembro no me tendria que generar instancia pero lo hace*/
run NuevoMiembroNoEsContador {some c1,c2 : Colegio, p : Persona | (p !in Contador) and agregarMiembro[c1,c2,p]}

/*Caso de exito:
El nuevo miembro debe pertenecer al consejo directivo de un colegio nacional, pero si no pertenece a uno igualmente genera instancia
Duda: No dice en ningun lado que la persona no pueda estar en 2 consejos al mismo tiempo*/
run NuevoMiembroPerteneceProvincial {some c1,c2 : Colegio, c3 : Provincial, p : Persona | (p in c3.titulares) and agregarMiembro[c1,c2,p] }

							/*INCISO C: Probando agregarMiembroV2*/
--3 casos de no exito

run ColegioNoProvincialV2 {some c1,c2: Nacional, p : Persona | agregarMiembroV2[c1,c2,p]}


run MiembroExistenteV2 {some c1,c2 : Colegio, p: Persona | (p in c2.titulares) and agregarMiembroV2[c1,c2,p]}


run NuevoMiembroNoEsContadorV2 {some c1,c2 : Colegio, p : Persona | (p !in Contador) and agregarMiembroV2[c1,c2,p]}

--3 casos de exito
run PersonaPerteneceNacional {some c1,c2: Colegio ,c3: Nacional, p : Persona | (p in c3.titulares) and agregarMiembro[c1,c2,p] }




