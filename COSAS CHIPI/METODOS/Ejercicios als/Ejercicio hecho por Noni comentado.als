--===================================================
// Modelo original 

sig Colegio {	
			miembros: set Persona,
			titulares: set Persona,
			suplentes: some Persona,
			id: one ID
	}
	
sig Provincial, Nacional extends Colegio {}
	
sig ID {}
	
sig Persona {
			dni: one DNI,
			matricula: set Matricula
	}
	
sig Contador, Abogado, Farmaceutico in Persona {} 
	
sig DNI {}
	
abstract sig Matricula {}
	
sig MatriculaC, MatriculaA, MatriculaF extends Matricula {}

-------- Hechos ------
//Toda persona puede tener a lo sumo un titulo, quiere decir que tiene uno o cero. 
fact {all p: Persona | (p in Contador) or (p in Abogado) or (p in Farmaceutico)}

//esta diciendo que la matricula es unica, no pueden tener dos personas(se fija en el DNI) la misma matricula
fact {all p1, p2: Persona | (p1.dni != p2.dni) implies (p1.matricula != p2.matricula)}

//Un colegio no puede tener el mismo ID
fact {all disj c1, c2: Colegio | c1.id != c2.id} 

//Ningun consejero de un colecgio pude ser titular y suplente al mismo tiempo
fact {all c: Colegio | c.titulares != c.suplentes}

//los miembros son la suma de los titulares y suplentes
fact {all c: Colegio | c.miembros = c.titulares + c.suplentes}
// Todos los miembros de un colegio poseen la misma profesion y se encuentran matriculados para dicha profesion, siendo esa profesion la que determina la categorıa del colegio
fact {all disj p1, p2: Persona, c: Colegio | ((p1 in c.miembros) and (p2 in c.miembros)) 
								implies 
								(
									mismaProfesion[p1, p2] and 
									((some p1.matricula) or (some p2.matricula))
								) 
}
//la cantidad de consejeros suplentes no puede superar a la cantidad de titulares
fact {all c: Provincial | #c.suplentes =< #c.titulares }

// un colegio nacional posee entre 1 y 4 consejeros titulares
fact {all c: Nacional | #c.titulares < 5 }

//predicado para misma profesion
pred mismaProfesion[p1, p2: Persona] {
	(p1+p2 in Contador) or
	(p1+p2 in Abogado) or 
	(p1+p2 in Farmaceutico)
}

--------------------- COMANDOS -----------------

// Propósito: ver si es posible que exista un colegio sin ID
run ColegioSinID { some c: Colegio | c.id = none } 
-- El comando genera instancias. La primera instancia generada es tal que existe un colegio sin ID.
-- No se cumple la restricción: "Los colegios poseen un número que los identifica"

// Propósito: verificar que el ID es lo que idetifica a un colegio --> El ID es unívoco para cada colegio
check IDColegioUnivoco { no c1, c2: Colegio | c1.id = c2.id }
-- El comando genera contraejemplos. El primer contraejemplo generado muestra c1= c2

// Propósito: verificar que el ID es lo que idetifica a un colegio --> El ID es unívoco para cada colegio
check IDColegioUnivocoV2 { no disj c1, c2: Colegio | c1.id = c2.id }
-- El comando no genera contraejemplos. La propiedad pareciera ser válida

// Propósito: mismo que el comadno IDColegioUnivocoV2 pero agrandando el scope
check IDColegioUnivocoV3{ no disj c1, c2: Colegio | c1.id = c2.id } for 10
-- El comando no genera contraejemplos. La propiedad "es válida" (es válida para el scope considerado)


// Propósito: ver si es posible que existan átomos de cada signatura
check ExistenAtomos { (some DNI) and (some Persona)  and (some Colegio) and (some ID) and (some Matricula) and (some Provincial) and (some Nacional) and (some MatriculaA) and (some MatriculaC) and (some MatriculaF) and (some Contador) and (some Abogado) and (some Farmaceutico)}
-- El comando generó contrajeemplos. El primer contraejemplo es tal que (entre otras cosas) no existen Farmacéuticos.
--> No debería haber usado un check!

// Propósito: ver si es posible que existan átomos de cada signatura
run ExistenAtomosV2 { (some DNI) and (some Persona)  and (some Colegio) and (some ID) and (some Matricula) and (some Provincial) and (some Nacional) and (some MatriculaA) and (some MatriculaC) and (some MatriculaF) and (some Contador) and (some Abogado) and (some Farmaceutico)}
-- El comando genera instancias. 
--> Sería recomendable probar esto con comandos separados 

// Propósito: ver si es posible que existan tuplas en cada relación del Colegio
run RelacionesNoVaciasColegio { (some miembros) and (some titulares)  and (some suplentes) and (some id)}
-- El comando genera instancias.

// Propósito: ver si es posible que existan tuplas en cada relación de la Persona
run RelacionesNoVaciasPersona { (some dni) and (some matricula)}
-- El comando genera instancias.

// Propósito: ver si toda persona se encuentra identificada por su DNI --> Toda persona tiene DNI
check TodasLasPersonasTienenDNI { no p: Persona | p.dni = none } for 10
-- El comando no genera contraejemplos.

// Propósito: ver si toda persona se encuentra identificada por su DNI --> Ver si es posible que exista una persona sin DNI
-- Comando equivalente al anterior
run ExistePersonaSinDNI {} // << HACER! >>

// Propósito: ver si toda persona se encuentra identificada por su DNI --> El DNI es unívoco
check DNIUnivoco { no disj p1, p2: Persona | p1.dni = p2.dni } for 10
-- El comando genera contraejemplos. En el primer contraejemplo generado existen 2 personas (Persona$7 y Persona$x8) que comparten DNI (DNI$0)

// Propósito: validar que "toda persona tiene a lo sumo un titulo/profesion"
-- << HACER! >>


/*
	De acuerdo a lo discutido en clase, la estrategia a adoptar para la verificación formal de modelos puede resumirse de la siguiente manera: 

	1) Definir comandos para validar el modelo brindado contemplando la definición de signaturas y sus relaciones, y las restricciones modeladas mediante hechos.
	Explorar la respuesta del analizador ante la ejecución de dichos comandos, describiendo las características evidenciadas (tanto aquellas correspondientes a propiedades deseadas, como las correspondientes a irregularidades).

	IMPORTANTE: Todo el proceso de verificación en esta etapa debe realizarse considerando el modelo original, SIN REALIZAR CAMBIOS SOBRE EL MISMO.	

	OBSERVACIÓN: Al momento de validar alguna característica particular del modelo mediante la ejecución de algún comando para dicho propósito
	es posible que en las instancias o contraejemplos generados por el analizador se observen irregularidades adicionales. 
	Es decir, irregularidades que no fueron buscadas explícitamente mediante las restricciones adicionales añadidas al comando ejecutado. 
	Esto también puede ser considerado en la validación. Simplemente, al describir las características de la instancia/contraejemplo obtenido
	se recomienda hacer mención a la observación de las irregularidades adicionales describiéndolas explícitamente e indicando que fueron
	detectadas mediante la ejecución de un comando no específico (es decir, mediante un comando definido para otro propósito).

	2) Identificar los cambios que habría que realizar sobre el modelo brindado, ya sea mediante la modificación de la definición de signaturas y/o relaciones, 
	mediante la modificación de hechos, o mediante el añadido de elementos (signaturas/relaciones/hechos) no contemplados previamente.
	
	3) Realizar una copia del archivo .als elaborado hasta el momento y trabajar sobre la nueva copia. 
	Realizar sobre el modelo las modificaciones identificadas en el punto 2).

	3) Definir comandos para validar el modelo resultante del punto 3) y describir los resultados obtenidos a partir de la ejecución de los comandos definidos. 
	Asegurarse de considerar todos los aspectos contemplados en el proceso original de verificación.
*/






