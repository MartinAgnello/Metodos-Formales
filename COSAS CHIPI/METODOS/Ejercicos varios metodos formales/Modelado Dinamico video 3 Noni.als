sig Biblioteca { coleccion: set Libro }

sig Libro { escritoPor: set Autor,
		  genero: one GeneroLiterario }

sig Autor{ }

sig Novelista, Poeta, Periodista extends Autor{ }

abstract sig GeneroLiterario{ }

one sig Epico, Lirico, Dramatico extends GeneroLiterario { }

--------------------------------------------------------------------------------------
// Todos los fact hacen "no es posible que haya novelistas y poetas que escriban libros en comun"
//alternativa 1 
fact { all l:Libro | no a1,a2: Autor | (a1 in Novelista) and (a2 in Poeta) and (a1 in l.escritoPor ) and (a2 in l.escritoPor) }
//alternativa 2
fact { all l:Libro | no a1,a2: Autor | (a1 in Novelista) and (a2 in Poeta) and (a1 in autores[ l ] ) and (a2 in autores[ l ] ) }
//alternativa 3
fact { all l:Libro | no a1,a2: Autor | (a1 in autoresNovelistas[ l ] ) and (a2 in autoresPoetas[ l ]) }


-------------------------------------------------------------------------------------------------
//Funciones 

// Funcion que se encarga de obtener el conjut de autores de un libro
fun autores[ l: Libro]: set Autor {
	l.escritoPor
}

// Funcion para obetener autores novelistars de un libro
fun autoresNovelistas[ l: Libro]: set Novelista{
	autores[ l ] & Novelista
}
// Funcion para obetener autores peotras de un liubro
fun autoresPoetas [ l:Libro ]: set Poeta {
	autores [ l ] & Poeta
}
// Funcion para obtener autores de una clase dada
fun autoresDeClase [l: Libro, clase: set Autor]: set Autor {
	autores[ l ] & clase
} 

//Funcion para obtener el conjunto de libors de una biblioteca que pertenecen a un genero dado

fun librosDeGenero[ b:Biblioteca, g: GeneroLiterario]: set Libro {
// el conjunto de libros tales que pertenece a la coleccion de la biblioteca(b) y es su genero literario es g 
	{l:Libro | (l in b.coleccion) and (l.genero = g) }
}

--------------------------------------------------------------------
// Asercion: funcion autores es equivalente a autoresDeClase utilizando a Autor

assert autoresEquivaleAautoresDeClase { 
	all l: Libro | autores [ l ] = autoresDeClase[ l, Autor ]
}
----------------------------------------------------------------------------------------
//Predicados: Hacemos predicados para poder modificar(evolucionar) un atomo
// Predicado que modele el comportamiento de agregar un libro a una bibilioteca (sin restricciones)
-- version 1: verdadero solo cunado el libro efectivamente se agrega a la coleccion de la biblioteca
-- version 2: verdadero siempre(cuando se agrega el libro o no)
pred agregarV1[ l:Libro, bi, bf: Biblioteca ]{
//bi = biblioteca inicial, bf = biblioteca final
 
	-----Precond: el libro no pertenece a la biblioteca inicial
	(l !in bi.coleccion) and
	-----Postcond: se agrega en biblioteca inicial el libro = a biblioteca final. El + es UNION
	(bf.coleccion = bi.coleccion + l)
}

pred agregarV2 [l: Libro, bi,bf: Biblioteca] {
	---Postcond: 
	(bf.coleccion = bi.coleccion + l)
	
}

//Predicado para eliminar libros de la coleccion de una biblioteca - Solo tiene exito cuando efectivamente se elimina el libro

/* Ademas deben verificarse las siguientes restricciones: ESTO ES COSAS EXTRA QUE AGREGO NONI
	- El libro a eliminar no puede ser de genero Epico
	- El libro a eliminar debe poseer autores
	-Luego de eliminar el libro, la biblioteca no puede tener menos de tres libros del genero al cual pertenece el libro eliminado

*/
pred eliminar [l:Libro, bi, bf:Biblioteca ]{
	---Precond
	(l in bi.coleccion) and // El libro tiene que pertenecer(IN) a la coleccion de la biblioteca de la cual se lo quiere eliminar
	(l.genero != Epico) and //El libro no tiene que ser de genero Epico. Esto se hace asi porque genero solo tiene un solo Genero(usa ONE)
	(some autores[ l ])and //(autores[ l ] != none) // #autores[ l ] > 0 El libro a eliminar debe poseer autores. NONE representa al conjunto Vacio

	--Postcond
	(bf.coleccion = bi.coleccion - l ) and // El libro se elimino de la coleccion de al biblioteca original. es la bf sin el libro eliminado
	(#librosDeGenero[bf, l.genero] >= 3)// el conjunto librosDeGenero[bf, l.genero] tenga de cantidad 3 o mas
	
}


---------------------------------------------------------------------------------------
run {}

check autoresEquivaleAautoresDeClase {} for 10

// exista algun libro(some l:Libro) tal que( | ) su cantidad de autores( #autores[ l ]) que sea 3 o mas(>= 3)
run algunLibroConAlMenos3Autores { some l: Libro | #autores[ l ] >=3 } for 5 
// el conjunto lo ponemos entre { } pongo el tipo primero, en este caso l:Libro y luego las condiciones que quiero
// { l: Libro | #autoresDeClase[ l, Novelista ] >= 2 } conjunto de libros que tiene 2 o mas autores de tipo Novelistas
// el { #{X}>1} estoy diciendo que quiero mas de un caso del conjunto X. 
run masDeUnLibroConAlMenos2AutoresNovelistas { #{ l: Libro | #autoresDeClase[ l, Novelista ] >= 2 } > 1 }

// que exista un libro y blibliotecas, tal que agregarV1 tenga exito
run agregarV1CasoExito {some l:Libro, bi,bf: Biblioteca | agregarV1[ l,bi,bf ] }

// que exista un libro y bibliotecas, tal que agregarV1 tenga exito y a su vez bi(biblioteca inicial) no tenga nada en su coleccion
run agregarV1CasoExistoBibliotecaVacia {some l: Libro, bi, bf: Biblioteca | agregarV1[ l, bi, bf ] and (no bi.coleccion) }

// que exista un libro y bibliotecas, tal que agregarV1 tenga exito y a su vez bi(biblioteca inicial) tenga ALGO(en este caso son libros) en su coleccion
run agregarV1CasoExitoBibliotecaNoVacia{some l:Libro, bi, bf: Biblioteca | agregarV1[ l,bi,bf ] and (some bi.coleccion) }

// ahora es igual a los anteriores pero con agregarV1 sin exito, para eso utilizo la palabra NOT agregarV1
run agregarV1CasoNoExisto {some l:Libro, bi,bf: Biblioteca | not agregarV1[l,bi,bf] }

// como siempre agregarV2 tiene exito lo que hago es agregar la precondicion de agregarV1(no entiendo porque lo hace)
run agregarV2CasoExitoSeAgrega { some l:Libro, bi, bf:Biblioteca | agregarV2[ l,bi,bf ] and ( l !in bi.coleccion ) }

//como el anterior pero dando a agregarV2 no agrega, o sea bi y bf van a apuntar a los mismos libros
run agregarV2CasoExitoNoSeAgrega { some l:Libro, bi, bf:Biblioteca | agregarV2[ l,bi,bf ] and ( l in bi.coleccion ) }

// que exista algun libro, en dos bibliotecas, tal que al eliminar el libro (l) de biblioteca inicial(bi) de de resultante biblioteca final(bf) 
// en realidad cuando pongo tal que( | ) y un predicado, significa que va a tener exito ese predicado, en este caso solo tiene exito si se elimina.
//No genera instancias! Scope insuficiente, esto sucede porque al tener un scope de 3 y pedir que tenga al menos 3 de el genero luego de eliminar, 
// tendria que haber al menos 4 para que luego de eliminar quede 3
run eliminarCasoExito { some l:Libro, bi,bf:Biblioteca | eliminar [l,bi,bf]} 

// ahora funciona perfecto ya que agregue scope de 5
run eliminarCasoExito2 { some l:Libro, bi,bf:Biblioteca | eliminar [l,bi,bf]} for 5

// no exista ningun libro tal que eliminar...
run eliminarCasoNoExito { no l:Libro, bi,bf:Biblioteca | eliminar [l,bi,bf]}

//exista algun libro y alguna biblioteca que eliminar tenga exito y a su vez otro caso donde eliminar no tenga exito(por eso usa NOT),
// usa el signo ' para diferenciar, pero podria poner otro nombre, no cambia nada
run eliminarCasoNoExito2 { (some l:Libro, bi,bf:Biblioteca | eliminar [l,bi,bf]) and (some l':Libro, bi',bf':Biblioteca | not eliminar[ l',bi',bf' ])} for 5




















