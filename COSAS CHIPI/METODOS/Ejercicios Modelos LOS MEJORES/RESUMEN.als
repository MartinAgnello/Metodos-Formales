//RESUMEN DE CODIGO

/*
QUITAR un monitor de una all-in-one o de una notebook.
La cantidad de teclados y mouse de la computadora original 
no puede superar (en forma conjunta) su cantidad de monitores.
Luego del traspaso, la computadora deberá contar con al menos dos monitores.
*/
pred quitarMonitor[c1, c2: Computadora, p: Periferico]{
	-- pre
	// c1 y c2 tienen q ser AIO, o bien c1 y c2 tienen que ser notebook
	((c1 in All_In_One and c2 in All_In_One) or
	(c1 in Notebook and c2 in Notebook)) and // preguntar
	// Para poder eliminar un periferico tiene que estar en los perifericos de la computadora c1
	p in c1.perifericos and

	// p tiene que ser un monitor
	p in Monitor and

	// La cantidad de teclados y mouse de la computadora original no puede superar
	// (en forma conjunta) su cantidad de monitores.
	// USO & porque quiero el conjunto, yo cuando uso IN lo que hago validar si es un subconjutno pero no obtengo
	// mas que un "verdadero o falso"
	#(c1.perifericos & (Mouse + Teclado)) <= #(c1.perifericos & Monitor) and

	-- marco
	// c1 y c2 tienen el mismo numero de inventario
	c1.inv_comp = c2.inv_comp and

	-- post
	// la computadora no debe contar con al menos 2 monitores
	#(c2.perifericos & Monitor) >= 2 and 
	c2.perifericos = c1.perifericos - p
}
-----------------------------------------------------------------------------------------------------------------------
//REMPLAZAR
pred reemplazarPeriferico[c1, c2: Computadora, p1, p2: Periferico]{
	-- pre
	p1 in c1.perifericos and 
	p2 not in c1.perifericos and
	c1 in All_In_One and
	c2 in All_In_One and
	((p1 in Monitor and p2 in Monitor) or
	(p1 in Teclado and p2 in Teclado)) and
	p1 != p2 and 
	
	-- marco
	c1.inv_comp = c2.inv_comp and
	c1.perifericos - p1 = c2.perifericos - p2 and
	
	-- post
	//chequeo que p2 este dentro de los perifericos de c2
	p2 in c2.perifericos and
	// chequeo que p1 no este dentro de los perifericos de c2
	p1 not in c2.perifericos

}
-------------------------------------------------------------------------------------------------------------------
/*
cual modela el comportamiento de anadir una persona al conjunto de miembros de un colegio provincial de contadores. Esta accion es posible
siempre y cuando la persona pertenezca al consejo directivo de un colegio nacional para esa profesion
*/
pred agregarMiembro1[c1, c2: Colegio, p: Persona] {
	(no c3: Nacional | (p in c3.(titulares+suplentes))) and
	(p in c2.miembros) and
	(c1.titulares in c2.titulares) and
	(c1.suplentes in c2.suplentes)
}

---------------------------------------------------------------------------------------------------------------
// ANADIR una persona al conjunto de miembros de un colegio provincial de contadores. Esta accion es posible
// siempre y cuando la persona pertenezca al consejo directivo de un colegio nacional
pred agregarMiembro[c1, c2: Colegio, p: Persona] {
	-- PRE
	// siempre que agrego tengo que verificar que P(persona), no este en los miembros
	p not in c1.miembros and
	// el colegio puede ser Nacional o Provincial por ende, tengo que chequear que c1 sea provincial
	c1 in Provincial and
	// necesito saber que la persona p sea consejero de un colegio titular, persona solo tiene matricula y dni
	// la unica forma es pidiendo un colegio nacional(c3) que p este dentro de los titulares y suplentes de c3 y
	// p tiene que ser un contador ya que estamos hablando del colegio provincial de CONTADORES. 
	(some c3: Nacional | (p in c3.(titulares+suplentes)) and p in Contador)  and

	-- MARCO
	c2 in Provincial and
	// aca chequeo que tengan la misma cantidad de titulares 
	c1.titulares = c2.titulares and
	// misma cantidad de suplentes
	c1.suplentes = c2.suplentes and
	//mismos id
	c1.id = c2.id and

	-- POST
	//aca agrego a p= la forma es c2.miembros = c1.miembros UNIDO(+) p, en caso de eliminar seria (-)
	c2.miembros = c1.miembros + p
}
----------------------------------------------------------------------------------------------------------------------------------------------
/*
Defina una función que permita obtener el conjunto de abogados o farmacéuticos 
que son consejeros titulares del consejo directivo de al menos un colegio y 
son consejeros suplentes de a lo sumo un colegio.
*/
//Como vemos existe sin que haya una variable dentro del [ ]
fun incisoD []: set Persona {// retorna un conjunto de Persona
	// dice que son un conjunto de personas pero son abogados o farmaceuticos por eso hago la union(+) 
	{ p: (Abogado + Farmaceutico) |
		//son consejeros titulares de AL MENOS un colegio(some= 1 o mas)
		(some c1: Colegio | p in c1.titulares ) and
		// los suplentes tienen que tener A LO SUMO(lone = 0 o 1 ) colegios a cargo
		(lone c2: Colegio | p in c2.suplentes)
	} 
}

run testD { #incisoD[] > 1 }
run testD1 { some a: Abogado, f: Farmaceutico | a in incisoD[] and f in incisoD[] }

----------------------------------------------------------------------------------------------------------------------------------------------

/*
Defina una función que permita obtener el conjunto de abogados o farmacéuticos 
que son consejeros titulares del consejo directivo de al menos un colegio y 
son consejeros suplentes de a lo sumo un colegio.
*/
//Como vemos existe sin que haya una variable dentro del [ ]
fun incisoD []: set Persona {// retorna un conjunto de Persona
	// dice que son un conjunto de personas pero son abogados o farmaceuticos por eso hago la union(+) 
	{ p: (Abogado + Farmaceutico) |
		//son consejeros titulares de AL MENOS un colegio(some= 1 o mas)
		(some c1: Colegio | p in c1.titulares ) and
		// los suplentes tienen que tener A LO SUMO(lone = 0 o 1 ) colegios a cargo
		(lone c2: Colegio | p in c2.suplentes)
	} 
}

run testD { #incisoD[] > 1 }

//  dentro de un run: si llamamos varias veces a la misma funcion , puede retornar conjuntos distintos entre si?
run testD1 { some a: Abogado, f: Farmaceutico | a in incisoD[] and f in incisoD[] }


----------------------------------------------------------------------------------------------------------------------------------------------
pred doceCambios[b: Bicicleta] {
	//Caso 1: Un solo modulo de 12 cambios	
	( (one b.cambios) and (b.cambios in Doce) ) or
	// Caso 2: Dos modulos de 6 cambios
	( (#b.cambios = 2 ) and (b.cambios in Seis) ) or
	// Caso 3: 1 Modulo de 6 cambios y 2 modulos de 3 cambios
	( (#b.cambios = 3 ) and (b.cambios in Seis + Tres ) ) or
	( (#b.cambios = 4) and (b.cambios in Tres))

}
--------------------------------------------------------------------
//Las bicicletas playeras chicas con cambios tienen 3 cambios.
//Las bicicletas playeras medianas con cambios tienen un total de 3 o 6 cambios.
// SI TIENE CAMBIOS, pero puede ser mediana o chica y NO TENER CAMBIOS
fact G{  
	// va asi con in o tendria que utilizar el =
	all p:Playera | // no tiene cambios
			      (p.cambios = none ) or
			      // si es de rodado chico solo puede tener un cambio de 3 
			      ( (p.rod in Chico) and ( tresCambios[p]) ) or 
			      // si es de rodado mediano un total de 3 o 6 cambios, 
			      ( (p.rod in Mediano ) and ( (seisCambios[p]) or ( tresCambios[p]) ) )
}

--------------------------------------------------------------------------------------------------------------------------
//-------------AGREGAR libro---------------
// quiere agregar a una coleccion mixta, la coleccion resultante (luego de agregarlo) no debe poseer mas de dos categorias
// de libros, considerandose tambien a “no categorizado” como una categorıa.
pred agregarLibro[bib1, bib2:Coleccion, lib:Libro]{
	//Precondiciones
	//Siempre chequeo que no este lib(libro ha agregar) dentro de la coleccion de bib1 
	not(lib in bib1.librosCol) and
	//Asumimos que no se puede transformar una coleccion de simple a mixta
	((bib1 in Mixta and bib2 in Mixta) or (bib1 in Simple and bib2 in Simple)) and //No se indica en el enunciado que se cumpla esto
	//chequeo que ambos tengan el mismo identificador ya que son la "misma" biblioteca
	(bib1.ident = bib2.ident) and
	//Poscondicion
	(bib2.librosCol = bib1.librosCol + lib) and 
	//Marco
	// simpre biblioteca bib2 que es mixta tiene que cumplir que no exceda mas de dos categorias
	// bib2 es un subconjunto de mixta implica que no tiene mas de dos categorias
	((bib2 in Mixta) implies not(masDeDosCategorias[bib2]))
}

------------------------------------------------------------------------------------------------------------------------------------------------------------------------------


















