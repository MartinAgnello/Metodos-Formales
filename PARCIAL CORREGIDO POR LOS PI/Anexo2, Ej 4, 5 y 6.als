/* Sincronizacion de archivos en la nube
Modelo para un solo archivo */

open util/ordering[Estado] as ord

one sig Archivo { }
sig Actualizacion { }
sig Prioritaria extends Actualizacion { }
sig Estado {
	actualizacionesPendientes: set Actualizacion,
	ultimaActualizacion: set Actualizacion 				// CORREGIDO (*2)
}

// minima cantidad de solicitudes \\
fact { #Actualizacion >2 and #Prioritaria >0 } 

// definicion de estado válido
fact { all  e:Estado | 
	(e.actualizacionesPendientes & e.ultimaActualizacion) = none or  
	(e.actualizacionesPendientes + e.ultimaActualizacion) = none
}

// limitacion de la cantidad de solicitudes marcadas como última \\
fact { all e:Estado | #(e.ultimaActualizacion) <= 1 }				// CORREGIDO (*1)

fact { all e: Estado | #e.actualizacionesPendientes > 0 implies e.ultimaActualizacion != none }	// AGREGADO (*3)

/* --------------------------------------------------------------------------------------------------------------------------------------------------------------------

Definicion de facts y predicados para modelar dinámica

Descomentar para el inciso 3

------------------------------------------------------------------------------------------------------------------------------------------------------------------------ */
 
fact traces { Inicializar[ord/first] and
	all est: Estado-ord/last | let sigEst=est.next |
	LlegaActualizacion[est,sigEst] or
             	AplicarUltimaActualizacion[est,sigEst] or
             	AplicarActualizacionPrioritaria[est,sigEst] 
}

pred Inicializar[e: Estado] {
	e.actualizacionesPendientes=none and 
	e.ultimaActualizacion=none
}

pred LlegaActualizacion[e1,e2: Estado] {
	// no hay solicitudes
	some a: Actualizacion | (
		(e1.actualizacionesPendientes=none and 
		e1.ultimaActualizacion=none and
		e2.actualizacionesPendientes=e1.actualizacionesPendientes and 
		e2.ultimaActualizacion=a )
           	)
	or
	// hay solicitudes
	some a: Actualizacion | (
		(e1.ultimaActualizacion!=none and
		a!in (e1.ultimaActualizacion + e1.actualizacionesPendientes) and
		e2.actualizacionesPendientes=e1.actualizacionesPendientes+e1.ultimaActualizacion and 
		e2.ultimaActualizacion=a )
	)
}

pred AplicarUltimaActualizacionX[e1,e2: Estado] {
	//precondiciones
	e1.ultimaActualizacion != none and  -- hay una actualización para aplicar 
	
	( 
	((e1.ultimaActualizacion in (Actualizacion-Prioritaria)) 	 -- la ultima actualizaciones no es prioritaria y
	and
	(e1.actualizacionesPendientes&Prioritaria) = none    	-- no hay actualizaciones prioritarias pendientes
	)
	
	or
	( e1.ultimaActualizacion in Prioritaria )   		-- la ultima actualizacion es prioritaria
	) 
	
	and 
	
	// poscondiciones
	(some a : (e1.actualizacionesPendientes) |
		e2.actualizacionesPendientes = e1.actualizacionesPendientes - a  and
		e2.ultimaActualizacion = a
	)
}

// _NE: los estados no son disjuntos
run estadosIdenticos {some e1,e2 : Estado | 
	e1 = e2 and AplicarUltimaActualizacion[e1,e2]
} for 5 // No devuelve instancias.
// _E: los estados son disjuntos
run estadosNoIdenticos {some e1,e2 : Estado | 
	e1 != e2 and AplicarUltimaActualizacion[e1,e2]
} for 5 // Devuelve instancias de estados disjuntos adecuadamente. Cumple la restricción verificada.


// _NE: no se aplica la última actualización.
run noAplicaUltimaActualizacion {some e1,e2 : Estado | 
	e1.ultimaActualizacion = e2.ultimaActualizacion and AplicarUltimaActualizacion[e1,e2]
} for 5 // No devuelve instancias.
// _E: se aplica la última actualización.
run aplicaUltimaActualizacion {some e1,e2 : Estado | 
	e1.ultimaActualizacion != e2.ultimaActualizacion and AplicarUltimaActualizacion[e1,e2]
} for 5 // Devuelve instancias coherentes. Verifica la restricción correctamente.


// _NE: aparecen actualizaciones de más.
run actualizacionesDeMas {some e1,e2 : Estado | { some a : Actualizacion |
	a !in e1.actualizacionesPendientes and 
	a in e2.actualizacionesPendientes and 
	AplicarUltimaActualizacion[e1,e2] }
} for 5 // No devuelve instancias.
// _E: no aparecen actualizaciones de más.
run noActualizacionesDeMas {some e1,e2 : Estado | { some a : Actualizacion |
	e2.actualizacionesPendientes = e1.actualizacionesPendientes - a and 
	AplicarUltimaActualizacion[e1,e2] }
} for 5 // Devuelve instancias coherentes. Verifica la restricción correctamente.


// _NE: no elimina las actualizaciones pendientes al recibir una actualización prioritaria
run noEliminaActualizaciones {some e1,e2 : Estado | 
	e1.ultimaActualizacion in Prioritaria and
	#e2.actualizacionesPendientes > 0 and
	AplicarUltimaActualizacion[e1,e2]
} for 5
// Devuelve instancias de solicitudes de actualizaciones pendientes que no son eliminadas al recibir una prioritaria.
// Además, al borrar las actualizaciones pendientes, rescata una y la guarda como última actualización.
// No verifican las restricciones correctamente.


// _NE: hay actualizaciones pendientes pero no existe última actualización.
run hayPendientesYnoHayUltima {some e1,e2 : Estado | 
	e1.ultimaActualizacion !in Prioritaria and
	#e2.ultimaActualizacion = 0 and
	#e2.actualizacionesPendientes > 0 and
	AplicarUltimaActualizacion[e1,e2]
} for 5 // No devuelve instancias
// _E: hay actualizaciones pendientes y existe última actualización.
run hayPendientesYhayUltima {some e1,e2 : Estado | 
	e1.ultimaActualizacion !in Prioritaria and
	#e2.ultimaActualizacion = 1 and
	#e2.actualizacionesPendientes > 0 and
	AplicarUltimaActualizacion[e1,e2]
} for 5 // Devuelve instancias coherentes. Verifica la restricción correctamente.


// _NE: la nueva última actualización, que no es prioritaria, no está en el grupo de actualizaciones pendientes previa (apareción de la nada).
run ultimaActualizacionNoEsPendiente {some e1,e2 : Estado | 
	e1.ultimaActualizacion !in Prioritaria and
	e2.ultimaActualizacion !in e1.actualizacionesPendientes and
	AplicarUltimaActualizacion[e1,e2]
} for 5 // No devuelve instancias
// _E: la nueva última actualización, que no es prioritaria, está en el grupo de actualizaciones pendientes previa.
run ultimaActualizacionEsPendiente {some e1,e2 : Estado | 
	e1.ultimaActualizacion !in Prioritaria and
	e2.ultimaActualizacion in e1.actualizacionesPendientes and
	AplicarUltimaActualizacion[e1,e2]
} for 5 // Devuelve instancias coherentes. Verifica la restricción correctamente.


//---------------------------------------------------------------------------------------------------------------------------------------------------------------------//
// 5)

pred AplicarUltimaActualizacion[e1,e2: Estado] {
	//precondiciones
	e1.ultimaActualizacion != none and  -- hay una actualización para aplicar 
	(e1.actualizacionesPendientes & Prioritaria) = none and	// (*) ver detalle
	
	( 
	((e1.ultimaActualizacion in (Actualizacion-Prioritaria)) 	 -- la ultima actualizaciones no es prioritaria y
	and
	(e1.actualizacionesPendientes&Prioritaria) = none    	-- no hay actualizaciones prioritarias pendientes
	)
	
	or
	( e1.ultimaActualizacion in Prioritaria )   		-- la ultima actualizacion es prioritaria
	) 
	
	and 
	
	// poscondiciones
	(
	// Cuando la última actualización es prioritaria, 
	// se borran todas las actualizaciones pendientes en el siguiente estado
	// además de la última actualizaciónn aplicada.
	(e1.ultimaActualizacion in Prioritaria and e2.actualizacionesPendientes = none and e2.ultimaActualizacion = none)
	
	or
	
	// Y si la última actualización no es prioritaria, se aplica una actualización normal.
	(
	e1.ultimaActualizacion !in Prioritaria and
		(some a : (e1.actualizacionesPendientes) |
		e2.actualizacionesPendientes = e1.actualizacionesPendientes - a  and
		e2.ultimaActualizacion = a
		)
	)
	)
}

/* Agregue un comando para validar si es posible aplicar, haciendo uso de dicho predicado,
una actualización no prioritaria habiendo actualizaciones prioritarias pendientes.
En caso de que sea posible, corrija el modelo para evitarlo. */
run testEjercicio5 { some e1,e2 : Estado | { one p : Prioritaria |
	#e1.actualizacionesPendientes > 1 and
	p in e1.actualizacionesPendientes and
	AplicarUltimaActualizacion[e1,e2] }
} for 5

// (*) No debería ser posible aplicar actualizaciones actualizaciones no prioritarias
// habiendo actualizaciones prioritarias pendientes. La consistencia debe ser corregida o bien mediante un fact
// o bien agregando la condición en el predicado corregido.
// fact {all e : Estado | e.actualizacionesPendientes & Prioritaria = none }


//---------------------------------------------------------------------------------------------------------------------------------------------------------------------//


pred AplicarActualizacionPrioritaria[e1,e2: Estado] {
 	-- precondiciones
         	(  (  (e1.actualizacionesPendientes) & Prioritaria) != none ) and  -- hay actualizaciones prioritarias pendientes
	-- poscondiciones
	(
	some p: (e1.actualizacionesPendientes) & Prioritaria, e : e1.(^prev) | 
		e.ultimaActualizacion = p and
		e2.actualizacionesPendientes = e1.actualizacionesPendientes - (e.actualizacionesPendientes+p) and
		e2.ultimaActualizacion = e1.ultimaActualizacion
	)
}


//---------------------------------------------------------------------------------------------------------------------------------------------------------------------//
// 6)

/* Verificar si se cumple la siguiente propiedad para todos los estados:
	"Si se aplica una solicitud no prioritaria, no quedan solicitudes pendientes en el próximo estado."
Dejar expresado en un comentario cuál es la respuesta del analizador y su interpretación sobre la misma.
*/

check aplicaNoPrioritaria { all disj e1,e2 : Estado | { some a : Actualizacion | 
	(a in e1.ultimaActualizacion and a !in Prioritaria and AplicarUltimaActualizacion[e1,e2]) 
	implies (#e1.next.actualizacionesPendientes = 0) } 
} for 5

// No devuelve ningún contraejemplo. Cumple la propiedad para todos los casos.







