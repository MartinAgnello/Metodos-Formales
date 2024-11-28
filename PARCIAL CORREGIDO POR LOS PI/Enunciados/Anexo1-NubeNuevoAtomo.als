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

pred AplicarActualizacion[a1,a2: Archivo]{
	-- precondición
	#a1.pendientes > 1 and
	-- poscondición
	(some a1.pendientes&Prioritaria implies 
		a2.pendientes = a1.pendientes - Prioritaria )  or
	((a1.pendientes&Prioritaria)= none implies 
		some act: Actualizacion | a2.pendientes = a1.pendientes - act ) 
	)
}


