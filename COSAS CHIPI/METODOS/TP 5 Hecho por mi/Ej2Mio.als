/* Por ultimo, un libro posee un conjunto de paginas y un grupo de
hasta tres marcadores, cada uno de los cuales puede referenciar a una pagina del libro.
*/


// Agrego el ordenamiento
open util/ordening[Estado] as est 

sig Libro { paginas: some Pagina,
	--marcadores: set Marcador 
	estados: set Estado
	
}

sig Marcador { pag: Pagina }

sig Pagina { }


sig Estado {marcadores: set Marcador }

// que dice este fact????
--fact {no m: Marcador, l: Libro | (m in l.marcadores) and (m.pag !in l.paginas) }
fact {no m: Marcador, l: Libro | (m in l.estados.marcadores) and (m.pag !in l.paginas) }

/*definir la condiciones del estado inicial */
// porque seria el estado inicial este???
// est/first.marcadores = primera pagina del libro, porque me pide que tenga si o si un marcador 
fact { no(est/first.marcadores)}

--fact {all l: Libro | #l.marcadores >= 0}
--fact {all l: Libro | #l.marcadores < 4}
// por estos dos fact saco la validez del estado, esta bien no?
pred estadoValido [e:Estado] {
	#e.marcadores >= 0 and #e.marcadores < 4
}

/* nos aseguramos que todos los estados son validos*/
fact {all e:Estado | estadoValido[e]}

------------------------- PUNTO C  ------------------------------------------

/* definir operaciones de cambio*/
pred agregarMarcador[e1,e2:Estado, m:Marcador]{
	m !in e1.marcadores and 
	// aca agrego el marcador 
	e2.marcadores = e1.marcadores + m
}

pred eliminarMarcador [e1,e2: Estado, m:Marcador]{
	m in e1.marcadores and
	e2.marcadores = e1.marcadores - m
}

// modificar seria que cambio el marcador m2 por el m1, entendi bien??
pred modificarMarcador [e1,e2: Estado, m1,m2: Marcador]{
	m1 in e1.marcadores and
	m2 not in e1.marcadores and
	e2.marcadores = e1.marcadores + m2 - m1
}


/* cambios de estados*/
// basicamente pongo lo del estado que son todos menos el ultimo hago lo del es= e next y luego pido lo que 
// necesito pra hacer los tres pred que hay, en este caso necesitaba los dos marcadores y listo
fact traces {
	all e:Estado-est/last | let es = e.next | some m1,m2: Marcador |
		agregarMarcador[e,es,m1] or eliminarMarcador[e,es,m1] or modificarMarcador [e,es,m1,m2]
}

// VERLO DESPUES
/* caso de exito: que se cumplan todos los estados*/
run { some e1,e2,e3,e4,e5,e6: Estado, m1,m2,m3,m4: Marcador |
	agregarMarcador[e1,e2,m1] and
	eliminarMarcador[e3,e4,m2] and
	modificarMarcador[e5,e6,m3,m4]
 } for 9














