open util/ordering[Estado] as ord

abstract sig Proceso {}

sig Lector, Escritor extends Proceso {}

one sig MemoriaCompartida {}

sig SeccionCritica {
	proceso: one Proceso,
	mc: MemoriaCompartida
}

sig Estado{
	sc1: lone SeccionCritica,
	sc2: lone SeccionCritica
}

fact cantidadProcesos { #Lector>=1 and #Lector<=3 and #Escritor>=1 and #Escritor<=3 }

fact init { no((ord/first).sc1) and no((ord/first).sc2) }

fact traces { all e: Estado-ord/last | let eSig = e.next | some p: Proceso | 
	ingreso[e, eSig, p] or
	egreso[e, eSig, p] 
	or realizarOperacion[e, eSig, p]
}

pred ingreso[e1, e2: Estado, p: Proceso]{
--	one p: Proceso |
		(no(e1.sc1) and -- pre
		e2.sc1.proceso = p and --post
		e1.sc2.proceso = e2.sc2.proceso) --marco
		or
		(no(e1.sc2) and -- pre
		e2.sc2.proceso = p and -- post
		e1.sc1.proceso = e2.sc1.proceso) --marco
}

pred realizarOperacion[e1, e2: Estado, p: Proceso]{
--	one p: Proceso|
		-- pre
		(p in e1.sc1.proceso) or (p in e1.sc2.proceso) and
		
		-- marco
		e1.sc1 = e2.sc1 and
		e1.sc2 = e2.sc2
}

pred egreso[e1, e2: Estado, p: Proceso]{
--	one p: Proceso |
		(
		e1.sc1.proceso = p and
		no(e2.sc1) and
		e1.sc2 = e2.sc2 --marco
		)
		or
		(
--		#e1.sc2.proceso = 1 and
		e1.sc2.proceso = p and
		no(e2.sc2) and
		e1.sc1.proceso = e2.sc1.proceso
		)
}

-- 1) a)
-- run general, encuentra instancias
run general { } for 9

run general_2 { #Proceso = 4 } for 9

-- no mas de 1 proceso en SC: correcto
run noMasDe1Proceso {
	some disj p1,p2: Proceso, e: Estado |
		(p1 in e.sc1.proceso and p2 in e.sc1.proceso) or
		(p1 in e.sc2.proceso and p2 in e.sc2.proceso) 
} for 9

-- primer estado vacio
/*
check primerEstadoSinPenSC { 
	all e1: ord/first | 
		#e1.seccionCritica = 0			
} for 9
*/

-- chequeamos cantidad de escritores. no deberia encontrar instancias, sin embargo encuentra

check cantEscritores {
	#Escritor >= 1 and #Escritor <= 3
}

-- chequeamos cantidad de lectores. no deberia encontrar instancias, sin embargo encuentra

check cantLector {
	#Lector >= 1 and #Lector <= 3
}


-- muy dificil hacer un check para esto
/*
check testIngreso {
	all disj e: Estado-ord/last | one p: Proceso | 
		ingreso[e,e.next] implies (
				#e.seccionCritica = 0 and
				p not in e.seccionCritica.MemoriaCompartida and
				p in e.next.seccionCritica.MemoriaCompartida
		)
} for 9 but 9 Estado
*/

fact { 
	all disj sc1,sc2: SeccionCritica | 
--		(#sc1.proceso!=0 and #sc2.proceso!=0) implies
			sc1.proceso != sc2.proceso 
}

fact {
	all p: Proceso |
		some sc: SeccionCritica |
			p in sc.proceso
}



-- no deberia encontrar instancias, y sin embargo encuentra
-- encontramos una instancia en la que hay mas de 1 proceso en la seccion critica
run testIngresoConRun {
--	#Proceso = 4 and
--	#SeccionCritica = 6 and
	some e: Estado, p: Proceso |
		ingreso[e,e.next,p] 
--		and #e.sc1 != 0
} for 9 but 5 Proceso, 7 Estado


run ingresoEscritorFallaPre {
	some e: Estado-ord/last, p: Proceso |
		ingreso[e, e.next, p] and
		#e.sc1.proceso>0 and 
		#e.sc2.proceso>0
} for 9


run ingresoEscritorFallaPos {
	some e: Estado-ord/last, p: Proceso |
		ingreso[e, e.next, p] and
		#e.sc1.proceso>0 and 
		#e.sc2.proceso=0 and 
		#e.next.sc1.proceso=0 and 
		#e.next.sc2.proceso=0
} for 9


run ingresoFalla {
	some e: Estado-ord/last, p: Proceso |
		ingreso[e, e.next, p] and
		#e.sc1.proceso=0 and 
		#e.sc2.proceso=0 and 
		#e.next.sc1.proceso=0 and 
		#e.next.sc2.proceso=0
} for 9











