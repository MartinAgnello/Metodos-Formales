sig Colegio {
	miembros: some Persona,
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
sig Contador, Abogado, Farmaceutico extends Persona {}
sig DNI {}
abstract sig Matricula {}
sig MatriculaC, MatriculaA, MatriculaF extends Matricula {}
fact {all disj p1, p2: Persona | p1.dni != p2.dni}
fact {no disj p1, p2: Persona | (some p1.matricula) and (some p2.matricula) and
(p1.matricula = p2.matricula)}
// fact {all disj c1, c2: Colegio | c1.id != c2.id} // debemos comentarlo
fact {Colegio = (Provincial+Nacional)}
fact {all c: Colegio | no (c.titulares & c.suplentes)}
fact {all c: Colegio | (c.titulares + c.suplentes) in c.miembros}
fact {all p: Persona | (some (MatriculaC & p.matricula)) implies (p in Contador)}
fact {all p: Persona | (some (MatriculaA & p.matricula)) implies (p in Abogado)}
fact {all p: Persona | (some (MatriculaF & p.matricula)) implies (p in Farmaceutico)}

fact {all p1, p2: Persona, c: Colegio | ((p1 in c.miembros) and (p2 in c.miembros))
		implies (mismaProfesion[p1,p2] and
				matriculadosParaMismaProfesion[p1,p2]) }

fact {all c: Provincial | (#c.titulares =< 3) and (#c.suplentes =< #c.titulares)}

fact {all c: Nacional | (#c.titulares < 5) and (#c.suplentes =< 2)}

pred mismaProfesion[p1, p2: Persona]
	{ (p1+p2 in Contador) or (p1+p2 in Abogado) or (p1+p2 in Farmaceutico) }

pred matriculadosParaMismaProfesion[p1, p2: Persona] {
	((some (p1.matricula & MatriculaC)) and (some (p2.matricula & MatriculaC))) or
	((some (p1.matricula & MatriculaA)) and (some (p2.matricula & MatriculaA))) or
	((some (p1.matricula & MatriculaF)) and (some (p2.matricula & MatriculaF)))
}



pred agregarMiembro1[c1, c2: Colegio, p: Persona] {
	(no c3: Nacional | (p in c3.(titulares+suplentes))) and
	(p in c2.miembros) and
	(c1.titulares in c2.titulares) and
	(c1.suplentes in c2.suplentes)
}

// Caso de exito 1
run agregarMiembroGeneral { some c1, c2: Colegio, p: Persona | agregarMiembro[c1, c2, p] }

----------------------------------------------------------------------------------------------------------------------------------------------

// Caso de no exito 1: p no deberia existir en c1 (no deberia generar instancias)
run agregarMiembroExistente { some c1, c2: Colegio, p: Persona | agregarMiembro[c1,c2,p] and
											     p in c1.miembros }
// Caso de no exito 2: p deberia existir en c2 (no deberia generar instancias)
run agregarMiembro_NoSeAgrega { some c1, c2: Colegio, p: Persona | agregarMiembro[c1,c2,p] and
											     p not in c2.miembros }
----------------------------------------------------------------------------------------------------------------------------------------------

// El MARCO se debe mantener:

// Caso de no exito 3: mismos titulares
run agregarMiembro_DistintosTitulares { some c1, c2: Colegio, p: Persona | agregarMiembro[c1,c2,p] and
											c1.titulares != c2.titulares
} for 7

// Caso de no exito 4: mismos suplentes
run agregarMiembro_DistintosSuplentes { some c1, c2: Colegio, p: Persona | agregarMiembro[c1,c2,p] and
											c1.suplentes != c2.suplentes
} for 7

// Caso de no exito 5: mismo ID
run agregarMiembro_DistintoID { some c1, c2: Colegio, p: Persona | agregarMiembro[c1,c2,p] and
											c1.id != c2.id
} for 7

----------------------------------------------------------------------------------------------------------------------------------------------

// Caso de no exito 3: que p no pertenezca a un colegio nacional
run AMnoColegioNacional {
	some c1, c2: Colegio, p: Persona | agregarMiembro[c1,c2,p] and 
						       (no c3: Nacional | 
								p in c3.(titulares + suplentes) 
								and p in Contador) 
}

check AMnoColegioNacional2 {
	all c1, c2: Colegio, p: Persona | agregarMiembro[c1,c2,p] implies
						       (some c3: Nacional | 
								p in c3.(titulares + suplentes) 
								and p in Contador) 
}
----------------------------------------------------------------------------------------------------------------------------------------------

// Caso de no exito: que no sea contador
run agregarMiembroNoContador {
	some c1, c2: Colegio, p: Persona |  agregarMiembro[c1,c2,p] and p not in Contador
}

// Caso de no exito: c1 y c2 debe ser un colegio provincial de contadores
run agregarMiembro_colegioProvincial { some c1, c2: Colegio, p: Persona | agregarMiembro[c1, c2, p] and
									c1 not in Provincial or
									c2 not in Provincial
}


----------------------------------------------------------------------------------------------------------------------------------------------
pred agregarMiembro[c1, c2: Colegio, p: Persona] {
	-- pre
	p not in c1.miembros and
	c1 in Provincial and
	(some c3: Nacional | (p in c3.(titulares+suplentes)) and p in Contador)  and

	-- marco
	c2 in Provincial and
	c1.titulares = c2.titulares and
	c1.suplentes = c2.suplentes and
	c1.id = c2.id and

	-- post
	c2.miembros = c1.miembros + p
}

----------------------------------------------------------------------------------------------------------------------------------------------

/*
Defina una función que permita obtener el conjunto de abogados o farmacéuticos 
que son consejeros titulares del consejo directivo de al menos un colegio y 
son consejeros suplentes de a lo sumo un colegio.
*/
fun incisoD []: set Persona {
	{ p: (Abogado + Farmaceutico) |
		(some c1: Colegio | p in c1.titulares ) and
		(lone c2: Colegio | p in c2.suplentes)
	} 
}

run testD { #incisoD[] > 1 }

//  dentro de un run: si llamamos varias veces a la misma funcion , puede retornar conjuntos distintos entre si?
run testD1 { some a: Abogado, f: Farmaceutico | a in incisoD[] and f in incisoD[] }


----------------------------------------------------------------------------------------------------------------------------------------------
pred colegioMismoTipo[c1, c2: Colegio]{
	( (c1 in Nacional and c2 in Nacional) or 
	  (c1 in Provincial and c2 in Provincial) )
}

fun consejoDirectivo[ c: Colegio ] :set Persona {
	{ c.(titulares + suplentes) }
}

/* 
Defina un predicado que modele el comportamiento de realizar el traspaso de un consejero
suplente del consejo directivo de un colegio a su conjunto de consejeros titulares: 
*/
pred suplenteATitular[c1, c2: Colegio, p: Persona] {
	/* pre: 
		la persona no debe formar parte del consejo directivo de un colegio 
		con distinto identificador que el colegio para el cual se está realizando el traspaso */
	(no c3: Colegio | (p in consejoDirectivo[c3] and (c3.id != c1.id))) and
	colegioMismoTipo[c1,c2] and // ESTO ES NECESARIO??? si ya verificamos que tengan el mismo ID

	-- marco, post
//	c1 != c2 and
	c1.id = c2.id and
	c2.titulares = (c1.titulares + p) and
	c2.suplentes = (c1.suplentes - p) and

	/* post:
		luego del traspaso, el colegio deberá contar con al menos un consejero suplente */
	#c1.suplentes >= 1 // esto podria ser una PREcondicion con #c1.suplentes >= 2 ? es lo mismo?
}

run suplenteATitularGeneral { some c1, c2: Colegio, p: Persona | suplenteATitular[c1, c2, p] } // como testeamos ésto ?

