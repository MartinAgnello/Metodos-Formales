open util/ordering[Estado] as est

sig Barco { }

sig Auto { }

abstract sig EstadoPuente { }

one sig Elevado, Bajo extends EstadoPuente { }

sig Estado {
	puente: one EstadoPuente,
	barcosEnEspera: set Barco, -- cambio de some a set
	autosEnEspera: set Auto,
	autosEnPuente: lone Auto -- cambio de one a lone
}

------------------------------------------------------------------------------------------------------------
// INCISO B
// este fact lo agregamos para solucionar  el check DosAutosDosBarcos
fact { #Barco >= 2 and #Auto >= 2 }

/* Toda instancia debe tener al menos 2 autos y 2 barcos, ya no encuentra instancias, lo cual esta bien*/
check DosAutosDosBarcos { #Barco >= 2 and #Auto >= 2 }


-- maximo 1 autos en puente
-- no encuentra instancias, lo cual es correcto
run MaxUnAuto { some e: Estado |  #e.autosEnPuente > 1 }

-- sin autos en puente
-- ahora encuentra instancias, lo cual es correcto
run CeroAutosEnPuente { some e: Estado |  #e.autosEnPuente = 0 }

-- con 1 auto en el puente
--  encuentra instancias, lo cual es correcto
run UnAutoEnPuente { some e: Estado |  #e.autosEnPuente = 1 }

-- chequeamos que pueda no haber barcos esperando
-- ahora encuentra instancias, lo cual es correcto
-- este porque es??? se que some es 1 o mas pero la pregunta que me hago, si no dice nada puede haber 0?? 
run NoBarcoEsperando { some e: Estado |  #e.barcosEnEspera = 0 }

----------------------------------------------
// INCISO C

/*definir la condiciones del estado inicial */ 
fact { no(est/first.barcosEnEspera) and no(est/first.autosEnEspera) and no(est/first.autosEnPuente) }

/* definimos un predicado para determinar la validez del estado*/
pred estadoValido[e: Estado] {
	-- si el auto esta en puente implica que el puente esta bajo, esto seria???
	((#e.autosEnPuente=1)implies(e.puente in Bajo))
}


/* nos aseguramos que todos los estados son validos*/
fact {all e:Estado | estadoValido[e]}


/* definir operaciones de cambio*/

-- llega un barco al puente, significa que ese barco pasa a estar en estado de espera no????
pred llegaBarco[e1,e2: Estado, b: Barco]{
	-- precondicion
	//el barco no esta en espera
	b !in e1.barcosEnEspera and

	-- marco
	// mismo puente
	e1.puente = e2.puente and
	//los autos se mantinien en el mismo estado e1 a e2
	e1.autosEnEspera = e2.autosEnEspera and
	e1.autosEnPuente = e2.autosEnPuente and 

	-- postcondicion
	// ahora se suma en espera el nuevo barco que llego
	e2.barcosEnEspera = e1.barcosEnEspera + b

}

pred llegaAuto [e1,e2: Estado, a:Auto]{
	-- precondicion
	a !in e1.autosEnEspera and
	
	--marco
	// los otros estados se mantienen ya que no sufren modificacion
	e1.puente = e2.puente and
	e1.barcosEnEspera = e2.barcosEnEspera and
	e1.autosEnPuente = e2.autosEnPuente and

	--postconcion
	//ahora se suma el auto en espera	
	e1.autosEnEspera = e2.autosEnEspera + a
}


-- sube un auto al puente (el puente debe estar bajo)
pred subeAutoPuente[e1,e2: Estado, a:Auto]{
	--precondicion 
	//auto tiene que estar en espera
	a in e1.autosEnEspera and
	//auto no tiene que estar en el puente
	a !in e1.autosEnPuente and
	// puente tiene que estar bajo
	e.puente = Bajo and
	
	--marco
	//puente es lo mismo
	e1.puente = e2.puente and
	//
	e2.barcosEnEspera = e1.barcosEnEspera and
	
	--postcondicion
	e2.autosEnPuente = e1.autosEnPuente + a and
	e2.autosEnEspera = e1.autosEnEspera -a 
	
}



pred bajaAutoDelPuente [e1,e2:Estado, a:Auto]{
	--precondicion
	//El auto debe estar en el puente
	a in e1.autosEnPuente and
	e1.puente = Bajo and
	
	--marco
	e1.puente = e2.puente and
	e1.barcoEnEspera = e2.barcosEnEspera and
	e1.autosEnEspera = e2.autosEnEspera and
	
	--postcondicion
	// tengo que sacar el auto en puente en e2
	e2.autosEnPuente = e1.autosEnPuente - a
  

}

pred cruzaUnBarco[e1,e2:Estado , b:Barco]{
	--precondicion
	b in e1.barcosEnEspera and
	e1.puente = Bajo and
	--marco
		e1.puente = e2.puente and 
	e1.autosEnPuente = e2.autosEnPuente and
	e1.autosEnEspera = e2.autosEnEspera and

	-- postcodicion
	e2.barcosEnEspera = e1.barcosEnEspera - b

}

-- cambia la posición del puente (cambia de elevado a bajo o de bajo a elevado)
pred cambiaPuente[e1,e2: Estado]{	
	-- pre
	
	-- marco
	e1.autosEnPuente = e2.autosEnPuente and
	e1.barcosEnEspera = e2.barcosEnEspera and
	e2.autosEnEspera = e1.autosEnEspera and

	-- post
	((e1.puente = Bajo and e2.puente = Elevado) or
	(e1.puente = Elevado and e2.puente = Bajo))
}




/* cambios de estados*/
fact traces {
	all e: Estado-est/last | let ef=e.next |
	(some b: Barco | 
		llegaBarco[e,ef,b] or 
		cruzaUnBarco[e,ef,b] ) 
	or
	(some a: Auto | 
		llegaAuto[e,ef,a] or 
		subeAutoAlPuente[e,ef,a] or
		bajaAutoDelPuente[e,ef,a] )
	or
	(cambiaPuente[e,ef])
}


// que hace el estado e1.^next ??? 
// probarlo separado, no todo junto porque de esta manera me  
run todosLosPreds { some e1: Estado-est/last, b: Barco, a: Auto | 
	{ some e: e1.^next | llegaBarco[e,e.next,b] } and
	{ some e: e1.^next | cruzaUnBarco[e,e.next,b] } and
	{ some e: e1.^next | llegaAuto[e,e.next,a] } and
	{ some e: e1.^next | subeAutoAlPuente[e,e.next,a] } and
	{ some e: e1.^next | bajaAutoDelPuente[e,e.next,a] }and
	{ some e: e1.^next | cambiaPuente[e,e.next] }
} for 8





--------------------- Inciso D---------------------------------

// Utilize el analizador para validar si es posible que ocurre:
// "Si hay un auto en el puente, puede mantenerse sobre el puente en forma indeterminada."

run autoEternoEnPuente {
	some e1: Estado-est/last1 |  #e1.autosEnPuente = 1 and
		{ all e2: e1.^next | #e2.autosEnPuente = 1 and #(e1.^next)>3 }

}for 9

/*
En la primer instancia se puede apreciar que un auto se mantiene en el puente
durante todos los estados menos los 2 primeros ya que en el primer estado está vacio
y en el segundo estado el auto debe estar en espera. en los siguientes estados el auto
siempre está en puente
*/





















