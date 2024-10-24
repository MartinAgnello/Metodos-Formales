/* Actualizacion de archivos en la nube  */

sig Archivo { pendientes: set Actualizacion} 
sig Actualizacion { }
sig Prioritaria extends Actualizacion { }
	
// minima cantidad de actualizaciones  por instancia
fact { #Actualizacion>2 } 

// no puede haber mas de dos actualizaciones prioritarias pendiente 
fact{all a: Archivo | a.pendientes&Prioritaria < 3}

-- AplicarActualización: el predicado debe satifacerse en caso que haya una actualizacion pendiente.
-- si hay alguna prioritaria debe aplicarse esta.
-- en caso de no haber prioritarias aplica alguna de las anteriores.
/*
pred AplicarActualizacion[a1,a2: Archivo]{	//la profe dice q por definicion a1 y a2 son !=
	-- precondición
	#a1.pendientes > 1 and	 	//el > es problema
	-- poscondición
	(some a1.pendientes&Prioritaria implies 
		a2.pendientes = a1.pendientes - Prioritaria )  or	//el or es un problema, a parte las 2 condiciones no son disjuntas
	((a1.pendientes&Prioritaria)= none implies 
		some act: Actualizacion | a2.pendientes = a1.pendientes - act ) 
	)
}*/

//CORRECCION
pred AplicarActualizacion[a1,a2: Archivo]{
	--precondicion
	some a1.pendientes and
	--postcondicion
	(some a1.pendientes & Prioritaria implies
	a2.pendientes = a1.pendientes - Prioritaria) and
	((a1.pendientes & Prioritaria)=none implies 
	some act:Actualizacion | a2.pendientes = a1.pendientes - act)
}
run {}


