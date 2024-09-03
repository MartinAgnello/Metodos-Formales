/*
	SUGERENCIAS PARA EL USO DE LA HERRARMIENTA: 
	
	* 	Setear verborragia del analizador (para observar el scope en cada ejecuciÃ³n de comandos):
		Options --> Message Verbosity --> Medium 
	
	*  	Una vez definido el modelo, visualizar el mismo: 
		Execute --> Show Metamodel

	* 	(A elecciÃ³n): Para visualizar automÃ¡ticamente las instancias generadas por el analizador
		Options --> Visualize Automatically --> Yes
		
		OBS: Si no se utiliza la visualizaciÃ³n automÃ¡tica, para visualizar la instancia generada:
		- Hacer click en "Instance/Counterexample" found; 
		- Utilizar el atajo "Show" del menÃº; o 
		- Execute --> Show Latest Instance	


	*	Se recomienda explorar las diferentes vistas para una instancia generada del modelo.
		Cada vista resulta Ãºtil en funciÃ³n de lo que se quiera observar para la instancia generada.
		En cierto aspecto, tambiÃ©n es una cuestiÃ³n de gustos :) 

	*	Recordatorio - EjecuciÃ³n de comandos: 
		
		- 	Ante mÃºltiples definiciones de comandos, el atajo "Execute" ejecuta el PRIMER comando RUN
			que se encuentre definido.
		-	Ante mÃºltiples definiciones de comandos, accediendo al menÃº "Execute" puede seleccionarse
			el comando que se desea que ejecute el analizador.
*/ 

-------------------------- Modelo --------------------------

sig  Biblioteca { coleccion: Libro -> Autor} // (*) Adaptar el modelo: EJERCICIO!
sig  Libro { escritoPor: set Autor}
abstract sig  Autor { }

sig Novelista, Poeta extends Autor { }
sig Periodista in Autor { }

-------------------------- Facts --------------------------

fact {
			all b: Biblioteca | (b.coleccion)  in escritoPor //(FACT 1)

			all l: Libro | no a1, a2: Autor | 	(a1 in Novelista) and 
															(a2 in Poeta) and 		
														 	(a1 in l.escritoPor) and 
															(a2 in l.escritoPor) // (FACT 2)

			-- FormulaciÃ³n alternativa para FACT 2: identificar los autores directamente como Poeta y Novelista:
			//	all l: Libro	| no p: Poeta, n: Novelista | .... [modificar restricciÃ³n de manera acorde] 

		
			
			-- EJERCICIO! // (FACT 3)
			/*
				 RestricciÃ³n que determine que la informaciÃ³n almacenada en la colecciÃ³n es COMPLETA
			     con respecto a los autores de los libros, de acuerdo a lo especificado por la relaciÃ³n escritoPor.
				 Es decir, en la colecciÃ³n cada libro tiene a todos sus autores registrados.
			*/ 
}

-------------------------- Preds / Funs --------------------------

pred libroEstaEnBib [l: Libro, b: Biblioteca] {
		#l.(b.coleccion) > 0
}

--------------------

fun autoresLibroEnBib [l: Libro, b: Biblioteca]: set Autor {
			l.(b.coleccion) 
			/* 
				DefiniciÃ³n alternativa: 
				{a: Autor | a in l.(b.coleccion)}
			*/
}

-------------------------- Assertions --------------------------

assert noNovelistaPoetaMismoLibroBib {
	all b: Biblioteca | no l: Libro, a1, a2: Autor | libroEstaEnBib[l,b] and 
																	(a1 in autoresLibroEnBib[l,b]) and 
																	(a1 in Novelista) and 
																	(a2 in autoresLibroEnBib[l,b]) and 
																	(a2 in Poeta)
}

// Comando Num 1
check noNovelistaPoetaMismoLibroBib
/* 
	La aserciÃ³n noNovelistaPoetaMismoLibroBib se verifica para el scope por defecto (3)
	Esto se debe a que la restricciÃ³n impuesta por FACT 2 tambiÃ©n aplica a la informaciÃ³n 
	almacenada en la colecciÃ³n de una biblioteca, dada la restricciÃ³n impuesta por FACT 1.

	OBS: Si se remueve la restricciÃ³n impuesta por FACT 1, la aserciÃ³n deja de valer (chequearlo!)
*/

--------------------
/* AserciÃ³n no vista en clase */
-- Si se quisiera chequear la situaciÃ³n descripta por FACT 1 mediante una aserciÃ³n:
assert noRelLibroAutorDesconocidaEnBib {
		all b: Biblioteca | no r: Libro -> Autor | (r in b.coleccion) and (r ! in escritoPor)
}

// Comando Num 2
check noRelLibroAutorDesconocidaEnBib 


-------------------------- Generate Instances --------------------------
// Comando Num 3
-- Generar una instancia del modelo sin restricciones adicionales
run { } //Default scope = 3

--------------------
// Comando Num 4
-- Generar una instancia en la que haya mÃ¡s de tres periodistas
run {# Periodista > 3}  // Default scope = 3
--> OBS: No es posible hallar una instancia que verifique esta restricciÃ³n utilizando el scope por defecto! 
-- Es necesario incrementar el scope (al menos para Autor)

--------------------
// Comando Num 5
-- ModificaciÃ³n del comando anterior, modificando el scope
run {#Periodista >3} for 4 Autor,  3 Libro, 3 Biblioteca //Incremento scope para Autor Ãºnicamente 
/*
	Al especificar un scope explÃ­cito para una signatura, debe hacerse lo mismo para las signaturas 
	necesarias, de modo tal que todas las signaturas de alto nivel queden cubiertas 
*/

--------------------
// Comando Num 6
-- Alternativa al comando #5, especificando scope para Novelista y Poeta explÃ­citamente 
-- en lugar de hacerlo sobre Autor
run { #Periodista > 3} for 2 Novelista, 2 Poeta, 3 Libro, 3 Biblioteca

--------------------
// Comando Num 7
-- Generar una instancia en la que la colecciÃ³n de una biblioteca posee informaciÃ³n "incompleta" 
-- en relaciÃ³n a la autorÃ­a de los libros que contiene
run { some b: Biblioteca | some (escritoPor - (b.coleccion))}
/*  
	OBS!!! Al generar una instancia con este comando, se observa que si bien la colecciÃ³n de una biblioteca 
	almacena informaciÃ³n correcta (por FACT 1), la misma puede ser incompleta ya que para un libro puede 
	haber autores faltantes (de acuerdo a lo establecido por la relaciÃ³n escritoPor)

	--> Para asergurar que esto no ocurra deberÃ­a definirse un fact adicional (FACT 3), o adaptarse el modelo (*)
*/

--------------------------------------------------------------------
--------------------/* Comandos no vistos en clase */--------------------
// Comando Num 8
-- Generar una instancia en la que algÃºn libro no posea autores (libro "anÃ³nimo" o de autorÃ­a no reconocida)
run {some l: Libro | #(l.escritoPor) = 0}

--------------------
// Comando Num 9
-- Generar una instancia en la que algÃºn libro no posea autores y forme parte de la colecciÃ³n de una biblioteca
run {some l: Libro, b: Biblioteca | (#l.escritoPor = 0) and (libroEstaEnBib[l,b]) }
/*
	El analizador no puede encontrar una instancia que satisfaga esta restricciÃ³n.
	Esto se debe a que, de la manera en la que estÃ¡ definido el modelo, la Ãºnica forma en la que un libro
	puede estar en la colecciÃ³n de una Biblioteca es que se encuentre en alguna tupla de dicha relaciÃ³n.
	De esta manera, el estar presente en alguna tupla implica la existencia de algÃºn autor para tal libro.

	--> 	OBS: Si se quisiera admitir la presencia de libros sin autores en la colecciÃ³n de una Biblioteca, 
			debe adaptarse el modelo (*)	
*/
