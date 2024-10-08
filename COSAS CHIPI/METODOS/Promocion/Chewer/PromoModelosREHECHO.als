open util/ordering[Estado] as ord

abstract sig Proceso {}

sig Lector, Escritor extends Proceso {}

one sig MemoriaCompartida {}

sig Estado{
	seccionCritica: Proceso -> lone MemoriaCompartida
}
fact cantidadProcesos { #Lector!=none and #Lector<=3 and #Escritor!=none }

fact init { no ((ord/first).seccionCritica) }

fact traces { all e: Estado-ord/last | let eSig = e.next | 
	ingreso[e, eSig] or
	egreso[e, eSig] or
	realizarOperacion[e, eSig]
}
pred ingreso[e1, e2: Estado]{
	one p: Proceso |
	--Pre
	no (p.(e1.seccionCritica)) and
	--Post
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


//--------------------> ejer 1 a) <------------------------------
//Caso de exito. son 7 entidad y 8 estados. 
run InstanciaGeneral{} for 7 but 8 Estado
//Caso de no exito
run masDe1Proceso{some disj p1, p2:Proceso, e:Estado | p1 in e.seccionCritica.MemoriaCompartida and p2 in e.seccionCritica.MemoriaCompartida} for 9
//Caso de exito. no va MAL CHEWER
check estadoinicialVacio{all e:ord/first | no(e.seccionCritica)} for 7 but 6 Estado
//Caso de exito. ESTO ES PORQUE HAY MAXIMO 3 PROCESOS DE CADA TIPO
check cantEscritoresCorrecto{#Escritor<=3 and #Escritor>0} for 7 but 10 Estado
//Caso de exito
check cantLectoresCorrecto{#Lector<=3 and #Lector>0} for 7 but 10 Estado
//---Ingreso---
//Caso de exito  <------CORROBORAR
check ingresoEscritor{all disj e:Estado-ord/last | one p:Proceso | not(p in e.seccionCritica.MemoriaCompartida) and
	((ingreso[e, e.next]) implies (p in e.next.seccionCritica.MemoriaCompartida))} for 7 but 8 Estado
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








