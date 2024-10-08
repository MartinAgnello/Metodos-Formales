open util/ordering[Estado] as ord

abstract sig Proceso {}

sig Lector, Escritor extends Proceso {}

one sig MemoriaCompartida {}

sig Estado{
seccionCritica: Proceso -> lone MemoriaCompartida
}

fact cantidadProcesos { #Lector!=none and #Lector<=3 and #Escritor!=none }

fact init { no ((ord/first).seccionCritica) }

fact traces { all e: Estado-ord/last | let eSig = e.next | ingreso[e, eSig] or
egreso[e, eSig] or 
realizarOperacion[e, eSig]
}

pred ingreso[e1, e2: Estado]{
	one p: Proceso |
	--Precondicion
	no (p.(e1.seccionCritica)) and
	--Postcondicion
	(e2.seccionCritica) = (e1.seccionCritica) + (p->MemoriaCompartida)
}

pred realizarOperacion[e1, e2: Estado]{
	one p: Proceso|
	--Pre
	((p->MemoriaCompartida) in (e1.seccionCritica)) and
	--Post
	((p->MemoriaCompartida) in (e2.seccionCritica))
}
	pred egreso[e1, e2: Estado]{
	one p: Proceso |
	--Pre
	((p->MemoriaCompartida) in (e1.seccionCritica)) and
	--Pos
	(e2.seccionCritica) = (e1.seccionCritica) - (p->MemoriaCompartida)
}

---Validar utilizando el analizador

//--------------------> ejer 1 a) <------------------------------
// Caso de exito: son 7 entidad y 8 estados lo que pido en el for
// Entidad: es todo lo que tenga un SIG dentro del esquema. En este caso:  Lector, Escritor, MemoriaCompartida, Estado.
// ESTA BIEN ESTO??
run InstanciaGeneral{} for 7 but 8 Estado

//Querio que me genere una instancia tal que dos procesos puedan ingresar a una seccion critica al mismo tiempo
run DosProcesosMismoTiempoSeccionCritica { some disj p1,p2: Proceso, e:Estado |
		(p1 in e.seccionCritica.MemoriaCompartida) and (p2 in e.seccionCritica.MemoriaCompartida) } for 7
//Como vemos me genera una instancia PREGUNTAR COMO EXPLICAR LA INSTANCIA, lo cual es una caso de NO EXITO
// pregunta bien como funcionan las -> , yo me acuerdo del Color: Color {Amarillo -> Rojo}, 

 //Caso de exito, vale la pena esto?? Muy redundante para mi, como seria buscar el caso inicial vacio?
check estadoinicialVacio{all e:ord/first | no(e.seccionCritica)} for 7 but 6 Estado

// Ahora busco si existe mas de 4 escritores, encuentra un contraejemplo. Por lo tanto es un caso de NO EXITO
// Ya que yo estaba esperando que no haya un contraejemplo porque no puede haber mas de 3 max por cada proceso 
run Maximo3Escritores{#Escritor>4}for 5 -- ESTA BIEN????

// Espero que me cree una instancia con 4 lectores, no devuelve una instancia. Por lo tanto es de EXITO,
// Ya que estoy pidiendo que haya como maximo 3 lectores y al pedir 4 y no devolver instancia es de EXITO. 
run Maximo3Lectores {#Lector>4} -- esta bien como justifico?

// SIRVEN ESTOS CHECKS???
check cantEscritoresCorrecto{#Escritor<=3 and #Escritor>0} for 7 but 10 Estado

check cantLectoresCorrecto{#Lector<=3 and #Lector>0} for 7 but 10 Estado



// Validacion del predicado Ingreso[e1,e2: Estado]

//Caso de exito
// para todos los estados menos el ultimo, tal que un proceso tal que el proceso p no este en seccion Critica(MemoriaComporatida) y
// ingreso e e.siguiente implica que ahora el preceso p esta en la seccion critica(memoria compartida) 
run ingresoEscritor{all disj e:Estado-ord/last | one p:Proceso | not(p in e.seccionCritica.MemoriaCompartida) and
	((ingreso[e, e.next]) implies (p in e.next.seccionCritica.MemoriaCompartida))} for 7 but 8 Estado ---- PREGUNTAR????


// Preguntar que mas????

-- HECHOS POR CHEWER

//Caso no exito
run ingresoEscritorFallaPre{one p:Proceso | some e:Estado-ord/last | 
	ingreso[e, e.next] and
	p in Escritor and
	(p in e.seccionCritica.MemoriaCompartida or #e.seccionCritica>0)} for 7 but 3 Estado


//Caso de no exito <--------- COMO SABER QUE PRECESO ESTA INVOLUCRADO EN EL INGRESO?
run ingresoEscritorFallaPos{one p:Proceso | some e:Estado-ord/last | 
	ingreso[e, e.next] and
	not(p in e.seccionCritica.MemoriaCompartida) and
	not(p in e.next.seccionCritica.MemoriaCompartida)} for 7 but 3 Estado

