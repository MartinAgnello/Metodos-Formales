open util/ordering[Estado] as ord

abstract sig Proceso {}
sig Lector, Escritor extends Proceso {}
//one sig MemoriaCompartida {}
sig Estado{					//Modificado
	seccionCritica1: lone Proceso,
	seccionCritica2: lone Proceso
}
fact cantidadProcesos { #Lector>0 and #Lector<=3 and #Escritor>0 and #Escritor<=3} //Modificado
fact init { no ((ord/first).seccionCritica1) and no ((ord/first).seccionCritica2)}
fact traces { all e: Estado-ord/last | let eSig = e.next | 
	ingreso[e, eSig] or
	egreso[e, eSig] or
	realizarOperacion[e, eSig]
}
pred ingreso[e1, e2: Estado]{
	some p: Proceso |
	(not(p in e1.seccionCritica1) and
	e2.seccionCritica1 = e1.seccionCritica1 + p and
	e2.seccionCritica2 = e1.seccionCritica2)
	or
	(not(p in e1.seccionCritica2) and
	e2.seccionCritica2 = e1.seccionCritica2 + p and
	e2.seccionCritica1 = e1.seccionCritica1)
}
pred realizarOperacion[e1, e2: Estado]{
	some p: Proceso|
	(p in e1.seccionCritica1 or p in e1.seccionCritica2) and	
	(e1.seccionCritica1 = e2.seccionCritica1) and
	(e1.seccionCritica2 = e2.seccionCritica2)
}
pred egreso[e1, e2: Estado]{
	some p: Proceso |
	((p in e1.seccionCritica1) and
	e2.seccionCritica1 = e1.seccionCritica1 - p and
	e2.seccionCritica2 = e1.seccionCritica2)
	or
	((p in e1.seccionCritica2) and
	e2.seccionCritica2 = e1.seccionCritica2 - p and
	e2.seccionCritica1 = e1.seccionCritica1)
}


//--------------------> ejer 1 a) <------------------------------
//Caso de exito
run InstanciaGeneral{} for 7 but 8 Estado
//Caso de no exito
run masDe1Proceso{some disj p1, p2:Proceso, e:Estado | (p1 in e.seccionCritica1 and p2 in e.seccionCritica1) or (p1 in e.seccionCritica2 and p2 in e.seccionCritica2)} for 9

//---Ingreso---

//Caso no exito
run ingresoEscritorFallaPre{some e:Estado-ord/last | 
	ingreso[e, e.next] and
	((#e.seccionCritica1>0) and( #e.seccionCritica2>0))} for 7 but 3 Estado
run ingresoEscritorFallaPreDos{some e:Estado-ord/last | 
	ingreso[e, e.next] and
	((#e.seccionCritica1>0) and( #e.seccionCritica2>0))} for 7 but 3 Estado
//Caso de no exito <--------- COMO SABER QUE PRECESO ESTA INVOLUCRADO EN EL INGRESO?
run ingresoEscritorFallaPos{some e:Estado-ord/last | 
	(ingreso[e, e.next] and (#e.seccionCritica1>0) and( #e.seccionCritica2=0)) and
		(#e.next.seccionCritica1=0 or #e.next.seccionCritica2=0)
	} for 7 but 3 Estado

//--------------------EJERCICIO 2---------------------

check todoLector{all p:Lector | all e:Estado-ord/last | 
	(not(p in e.seccionCritica1) and ingreso[e, e.next-ord/last] and (p in e.next.seccionCritica1)) implies
		(some e2:e.^next-ord/last | egreso[e2, e2.next] and (p in e2.seccionCritica1) and not(p in e2.next.seccionCritica1))
} for 8 but 12 Estado

check todoLector2{all p:Lector | all e:Estado-ord/last | 
	(not(p in e.seccionCritica2) and ingreso[e, e.next-ord/last] and (p in e.next.seccionCritica2)) implies
		(some e2:e.^next-ord/last | egreso[e2, e2.next] and (p in e2.seccionCritica2) and not(p in e2.next.seccionCritica2))
} for 8 but 12 Estado

//------------------EJERCICIO 3--------------------

fact todoLectorSALE{all p:Proceso | all e:Estado - ord/last | 
	(not(p in e.seccionCritica1) and ingreso[e, e.next-ord/last] and (p in (e.next-ord/last).seccionCritica1)) implies
		(egreso[e.next-ord/last, (e.next-ord/last).next] and not(p in (e.next-ord/last).next.seccionCritica1)) 	
}

fact todoLectorSALE2{all p:Proceso | all e:Estado - ord/last | 
	(not(p in e.seccionCritica2) and ingreso[e, e.next] and (p in e.next.seccionCritica2)) implies
		(egreso[e.next, e.next.next] and not(p in e.next.next.seccionCritica2))
}

//TODO ANDA JOYA      <<<<<<<<===============
