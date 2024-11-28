/* Actualizacion de archivos en la nube  */

sig Archivo { pendientes: set Actualizacion}
sig Actualizacion { }
sig Prioritaria extends Actualizacion { }

// minima cantidad de actualizaciones  por instancia
fact { #Actualizacion > 2 } 

// no puede haber mas de dos actualizaciones prioritarias pendiente 
fact{all a: Archivo | #a.pendientes&Prioritaria < 3}

-- AplicarActualización: el predicado debe satifacerse en caso que haya una actualizacion pendiente.
-- si hay alguna prioritaria debe aplicarse esta.
-- en caso de no haber prioritarias aplica alguna de las anteriores.

pred AplicarActualizacion[a1,a2: Archivo]{
	-- precondición
	#a1.pendientes > 1 and
	-- poscondición
	(
	(some a1.pendientes&Prioritaria implies 
		a2.pendientes = a1.pendientes - Prioritaria )  or
	((a1.pendientes&Prioritaria)= none implies 
		some act: Actualizacion | a2.pendientes = a1.pendientes - act ) 
	)
}

//-------------------------------------------------------------------------------------------------------------------------------------------------------------------//
// 1) 

// Prueba general para el modelo presentado:
run pruebaGeneral {some disj a1,a2 : Archivo | AplicarActualizacion[a1,a2]} for 5


// CASOS DE NO ÉXITO:
// a1 y a2 no son fases diferentes de un mismo archivo
run mismasFases {some a1,a2: Archivo | a1 = a2 and AplicarActualizacion[a1,a2] }
// Devuelve instancias en donde a1 y a2 son fases idénticas de un único archivo. No verifica la restricción correctamente.

// Se ejecuta una actualización normal antes que una prioritaria
run actNormalesPrimero {some a1,a2: Archivo | 
	( some actN : a1.pendientes - Prioritaria, actP : a1.pendientes&Prioritaria |
	a2.pendientes = a1.pendientes - actN and actP in a2.pendientes
	and  AplicarActualizacion[a1,a2] )
}
// Devuelve una instancia en donde la actualización normal se ejecuta primero. No verifica la restriccion correctamente.

// Aparecen acutalizaciones después de aplicar una.
run aparecenActualizaciones{some a1,a2: Archivo |
	( some act : Actualizacion |
	a2.pendientes = a1.pendientes + act and
	act !in a1.pendientes and 
	AplicarActualizacion[a1,a2] )
}
// Devuelve una instancia en donde aparecen nuevas actualizaciones pendientes en la 2da. fase. No verifica la restricción correctamente.


// CASOS DE ÉXITO:
// La actualización se efectúa de manera correcta para dos archivos.
run actualizacionCorrecta{some a1,a2: Archivo | 
	( some actu1, actu2 : Actualizacion |
	actu1 in a1.pendientes and actu2 in a1.pendientes and 
	actu1 !in a2.pendientes and actu2 in a2.pendientes and
	AplicarActualizacion[a1,a2] )
}
// Devuelve instancias donde las actualizaciones se efectúan de manera adecuada. Verifica la restricción correctamente.


//-------------------------------------------------------------------------------------------------------------------------------------------------------------------//
// 2) 

pred AplicarActualizacionCorregido[a1,a2: Archivo]{
	-- precondición
	#a1.pendientes >= 1 and		// de acuerdo al enunciado, se debe "tomar una actualización pendiente"
	
	-- invariantes
	a1 != a2 and
	
	-- poscondición
	(
	(some a1.pendientes&Prioritaria implies 
		a2.pendientes = a1.pendientes - Prioritaria )  and		// corrección de 'or' por 'and' (*)
	((a1.pendientes&Prioritaria)= none implies 
		some act: Actualizacion | a2.pendientes = a1.pendientes - act ) 
	)
	
	/* (*) Detalle: la corrección cubre dos restricciones corregidas:
		   no se ejecuta una actualización normal antes que una prioritaria
		   y no aparecen actualizaciones random luego de ejecutar una.
	*/
}


// CASOS DE NO ÉXITO:
run noHayActualizaciones {some a1,a2: Archivo | #a1.pendientes = 0 and AplicarActualizacionCorregido[a1,a2] }
run mismasFases2{some a1,a2: Archivo | a1 = a2 and  AplicarActualizacionCorregido[a1,a2] }
// Ninguno devuelve instancias. Las restricciones se verifican correctamente.

// CASOS DE ÉXITO:
run actualizacionCorrecta2 {some a1,a2: Archivo | 
	( some actu1, actu2 : Actualizacion |
	actu1 in a1.pendientes and actu2 in a1.pendientes and 
	actu1 !in a2.pendientes and actu2 in a2.pendientes and
	AplicarActualizacion[a1,a2] )
}
// Devuelve instancias donde la fase inicial tiene más actualizaciones que la segunda. El caso se verifica correctamente.

run primeroPrioritarias {some a1,a2: Archivo | 
	some actP : a1.pendientes&Prioritaria, actN : a1.pendientes - Prioritaria |
	a2.pendientes = a1.pendientes - actP and actN in a2.pendientes and
	AplicarActualizacion[a1,a2] 
}
// Devuelve instancias donde la actualización prioritaria se efectúa antes que la normal. El caso se verifica correctamente.



/*
Observación:
	Para los casos de no éxito conviene aumentar el scope siempre.
	Para los casos de éxito conviene aumentar el scope si no devuelve instancias.
*/


