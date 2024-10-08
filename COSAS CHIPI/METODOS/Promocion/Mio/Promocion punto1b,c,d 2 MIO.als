open util/ordering[Estado] as ord

abstract sig Proceso {}

sig Lector, Escritor extends Proceso {}

one sig MemoriaCompartida {}

sig SeccionCritica {
	proceso: one Proceso,
	mc: MemoriaCompartida
}


sig Estado {
-- porque se hace de esta manera???
--seccionCritica: Proceso -> lone MemoriaCompartida
	sc1: lone SeccionCritica,
	sc2: lone SeccionCritica
}

--fact cantidadProcesos { #Lector!=none and #Lector<=3 and #Escritor!=none }
fact cantidadProcesos { #Lector>=1 and #Lector<=3 and #Escritor>=1 and #Escritor<=3 }


--fact init { no ((ord/first).seccionCritica) }
// Inicialmente no hay procesos utilizando la seccion critica
fact init  { no((ord/first).sc1) and no((ord/first).sc2) }


fact traces { all e: Estado-ord/last | let eSig = e.next | some p: Proceso |
	ingreso[e, eSig,p] or
	egreso[e, eSig,p] or 
	realizarOperacion[e, eSig,p]
}


// Modifique ya que ahora tengo dos secciones criticas
// Lo que no entendia es porque antes no habia procesos (en el [ ] ) como se daba cuenta cual es el proceso???? 
pred ingreso[e1, e2: Estado, p:Proceso]{
	--one p: Proceso |
	(no(e1.sc1) and --precondicion
	 e2.sc1.proceso = p and --postcondicion
	e1.sc2.proceso = e2.sc2.proceso) -- marco
	or
	(no(e1.sc2) and --precondicion
	e1.sc1.proceso = e2.sc1.proceso and-- marco
	e2.sc2.proceso = p	--postcondicion
	)
}

pred realizarOperacion[e1, e2: Estado, p:Proceso]{
--	one p: Proceso|
	--Precondicion
	(p in e1.sc1.proceso) or (p in e1.sc2.proceso) and
	--((p->MemoriaCompartida) in (e1.seccionCritica)) and
	--((p->MemoriaCompartida) in (e2.seccionCritica))
	-- Marco
	e1.sc1 = e2.sc1 and
	e1.sc2 = e2.sc2
}


	pred egreso[e1, e2: Estado, p:Proceso]{
	--one p: Proceso |
	--((p->MemoriaCompartida) in (e1.seccionCritica)) and
	( 
	e1.sc1.proceso = p and
	no(e2.sc1) and
	--marco
	e1.sc2 = e2.sc2
	)
	or
	(
	e1.sc2.proceso = p and
	no(e2.sc2) and
	e1.sc1.proceso = e2.sc1.proceso
	)
	--(e2.seccionCritica) = (e1.seccionCritica) - (p->MemoriaCompartida)

}


check cantEscritores {
	#Escritor >= 1 and #Escritor <= 3
}

check cantLector {
	#Lector >= 1 and #Lector <= 3
}







