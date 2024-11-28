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

// ------------------------------------------------------------------------------------------------------------------------------------------------------------------//

run {}
/* (*1) Corro una prueba general y no devuelve instancias para ningún scope.
Observando el modelo, descubro una inconsistencia en la última restricción acerca de la cantidad de solicitudes marcadas como última.
De la forma dada, no podría haber actualizaciones (< 1), con lo cual modifico la relación a <= 1 para permitir 0 o 1 actualización. */

run casoSinActualizaciones{some e : Estado | #e.actualizacionesPendientes = 0 and #ultimaActualizacion = 0}
/* No devuelve instancias. No contempla el caso de un estado sin actualizaciones.
  (*2) Las actualizaciones pendientes están vinculadas a través de "set", es decir, cualquier cantidad,
  pero la última actualización está vinculada a través de "some", lo cual permite cualquier cantidad menos 0.
  Esto vuelve imposible evaluar el caso en donde no hay que aplicar actualizaciones.
*/

run noHayUltimaActualizacion{some e : Estado | #e.actualizacionesPendientes > 0 and #ultimaActualizacion = 0}
/* Devuelve instancias en donde hay actualizaciones pendientes, pero ninguna es la última actualización. Esto es incorrecto.
     (*3) Según el apartado "Llegada de una solicitud de actualización", cuando llega una solicitud de actualización
     debe registrarse como última actualización, lo cual implica que si hay al menos un actualización pendiente hay una última actualización.
*/


// CASOS DE NO ÉXITO:
// (1) Permite la última solicitud de actualización a más de una solicitud pendiente.
run unicaSolicitud { some e: Estado | #e.actualizacionesPendientes > 1 }

// (2) Permite la última solicitud de actualización aún con una solicitud prioritaria.
//run haySolicitudPrioritaria { some e: Estado | #Prioritaria > 1 }



/* --------------------------------------------------------------------------------------------------------------------------------------------------------------------

Definicion de facts y predicados para modelar dinámica

Descomentar para el inciso 3

------------------------------------------------------------------------------------------------------------------------------------------------------------------------ */
 /*
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

pred AplicarUltimaActualizacion[e1,e2: Estado] {
	//precondiciones
	e1.ultimaActualizacion !=none and  -- hay una actualización para aplicar 
	( 
		( 	( e1.ultimaActualizacion in (Actualizacion-Prioritaria)) and -- la ultima actualizaciones no prioritaria y
			(e1.actualizacionesPendientes&Prioritaria)=none    -- no hay actualizaciones prioritarias pendientes
	          )
	or
		(	e1.ultimaActualizacion in Prioritaria   -- la ultima actualizacion es prioritaia
		)
	) and  
	// poscondiciones
	 (some a: (e1.actualizacionesPendientes) |
			e2.actualizacionesPendientes = e1.actualizacionesPendientes - a  and
			e2.ultimaActualizacion= a
}

pred realizarActualizacionPrioritaria[e1,e2: Estado] {
 	-- precondiciones
         (  (  (e1.actualizacionesPendientes)&Prioritaria) != none ) and  -- hay actualizaciones prioritarias pendientes
         -- poscondiciones
	(
	some p: (e1.actualizacionesPendientes)&Prioritaria, e: e1.(^prev) | 
			e.ultimaActualizacion = p and
			e2.actualizacionesPendientes = e1.actualizacionesPendientes - (e.actualizacionesPendientes+p) and
			e2.ultimaActualizacion = e1.ultimaActualizacion
	)
}

*/
