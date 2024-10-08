sig Coleccion {
	ident: ID,
	librosCol: some Libro
}
sig ID { }
sig Simple, Mixta extends Coleccion { }
sig Libro {
	paginas: some Pagina,
	marcadores: set Marcador
}
sig Marcador {
	pag: Pagina
}
sig Academico, Recreativo in Libro { }
sig Pagina { }
fact {no (Coleccion - Simple - Mixta)}
fact { disj[Academico, Recreativo] }
/*
fact {no disj c1, c2: Coleccion | c1.ident = c2.ident}}
*/
fact {all l: Libro | #l.marcadores < 4}
fact {all m: Marcador, l: Libro | (m in l.marcadores) implies (m.pag in l.paginas)}
fact {all s: Simple | no l1, l2: s.librosCol | librosDistintaCategoria[l1, l2]}
pred librosDistintaCategoria[l1, l2: Libro]{
	(l1 in Academico and l2 in Recreativo) or
	(l1 in Academico and l2 in (Libro-Academico-Recreativo)) or
	(l1 in Recreativo and l2 in (Libro-Academico-Recreativo))
}
//-------------Agregar libro---------------
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
	
	((bib2 in Mixta) implies not(masDeDosCategorias[bib2]))
}
// lo que hace este predicado con una biblioteca
pred masDeDosCategorias[bib:Coleccion]{
	// si hay tres libros DISTINTOS(disj) tal que
	some disj lib1, lib2, lib3:Libro |
	// cada libro sea parte de la coleccion de la biblioteca
	(lib1 in bib.librosCol) and
	(lib2 in bib.librosCol) and
	(lib3 in bib.librosCol) and
	// si cada uno es de distinta categoria entre si 
	(librosDistintaCategoria[lib1, lib2]) and
	(librosDistintaCategoria[lib2, lib3]) and
	(librosDistintaCategoria[lib1, lib3])
}
//----------------tests---------------------------
run predBInstancia{some bib1, bib2:Coleccion, lib:Libro | agregarLibro[bib1, bib2, lib] } for 5

//Caso de no exito
run predBMixtaYMasDeDosCat{some bib1, bib2:Coleccion, lib:Libro | (bib1 in Mixta) and (masDeDosCategorias[bib2]) and (agregarLibro[bib1, bib2, lib])} for 7

//Test predMdd, Caso de exito
run PredMDDMasDeDosCat{some bib:Mixta, lib1, lib2, lib3:Libro | 
	(lib1 in bib.librosCol) and
	(lib1 in Academico) and
	(lib2 in bib.librosCol) and
	(lib2 in Recreativo) and
	(lib3 in bib.librosCol) and
	(masDeDosCategorias[bib])} for 4

//Test predMdd, Caso de no exito
run PredMDDDosCat{some disj  lib1, lib2: Academico, disj bib:Mixta, lib3:Recreativo | 
	(lib1 in bib.librosCol) and
	(lib2 in bib.librosCol) and
	(lib3 in bib.librosCol) and
	 #(bib.librosCol) = 3 and
	(masDeDosCategorias[bib])} for 3
