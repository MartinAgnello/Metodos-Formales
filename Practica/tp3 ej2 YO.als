sig Vehiculo {
	titulares: set Persona,
	autorizados: set Persona,
	placa: lone Patente
}

sig Proveeduria, Comercial, Gerencial extends Vehiculo {}

sig Patente {}

sig Persona {
	id: one DNI,
	carnet: lone LicenciaConducir
}

sig Mayoria18, Mayoria16, Menor in Persona {}

sig DNI {}

sig LicenciaConducir {}

fact {no Vehiculo - Proveeduria - Comercial - Gerencial}

fact {all v: Vehiculo | (some v.placa) implies (some v.titulares and #v.titulares < 3)}

fact {no v: Vehiculo | some (v.titulares & v.autorizados)}

fact {no v: Vehiculo | (no v.placa) and ((some v.titulares) or (some v.autorizados))}

fact {no disj p1, p2: Persona | (p1.id = p2.id)}

fact {no Persona - Menor - Mayoria16 - Mayoria18}

fact {no Menor & Mayoria16}

fact {no Menor & Mayoria18}

fact {Mayoria18 in Mayoria16}

fact {all p: Persona| (some titulares.p) implies (p in Mayoria18)}

fact {all p: Persona | (some autorizados.p) implies (p in Mayoria16)}

fact {all p: Persona | (some p.carnet) implies (p in Mayoria16)}

fact {all vg: Gerencial | lone vg.titulares}

fact {all vp: Proveeduria | #(vp.autorizados) < 4}

fact {no disj p1, p2: Persona | (some p1.carnet) and (some p2.carnet) and
					(p1.carnet = p2.carnet)}

fact {no disj v1, v2: Vehiculo | (some v1.placa) and (some v2.placa) and
					(v1.placa = v2.placa)}
-----------------------------------------------------------------------------------------------------------------
/*
añadir una persona al conjunto de personas autorizadas a manejar 
un veh´ıculo de proveedur´ıa. 
Esta accion es posible siempre y cuando: 
la persona posea licencia de conducir y 
la cantidad original de personas autorizadas a manejar el veh´ıculo no supere a la cantidad de titulares del mismo:
*/

pred agregarAutorizado[v1, v2: Vehiculo, p: Persona] {
	(one p.carnet) and
	(#v1.autorizados > #v1.titulares) and
	(p in v2.autorizados) and
	(v2.titulares = v1.titulares)
}

//añado una persona que ya esta en v1 por lo tanto no añadio a nadie, no tendria q generar instancia y la genera
run CasoNoExito1{some disj v1,v2: Vehiculo, p : Persona | p in v1.autorizados and agregarAutorizado[v1, v2, p]}

//los vehiculos no son de proveduria, no tendria q generar instancia y la genera
run CasoNoExito2{some disj v1,v2: Vehiculo, p: Persona | v1 !in Proveeduria and v2 !in Proveeduria and agregarAutorizado[v1, v2, p]}

//la persona posee licencia
run casoExito1{some disj v1,v2: Vehiculo, p: Persona | p.carnet != none and agregarAutorizado[v1, v2, p] }
//funciona bien porque  genera instancia 

//son mas las personas autorizadas que la cantidad de titulares del mismo, no tendria q generar instancia y la genera
run casoNoExito3{some disj v1,v2 : Vehiculo, p: Persona | #v1.autorizados > #v1.titulares and agregarAutorizado[v1, v2, p]  }

//para confirmar el caso de no exito3 chequeo si puedo generar el caso opuesto:
//son menos las personas autorizadas que la cantidad de titulares
run casoExito2{some disj v1,v2 : Vehiculo, p: Persona | #v1.autorizados < #v1.titulares and agregarAutorizado[v1, v2, p]  }
//como el caso de exito no genera instancia cuando los autorizados son menos que los titulares entonces, esta mal

--------------------------------------------------------------------------------------------------
/*
chequeos logicos:
la patente es distinta
el auto es de otro tipo
los autorizados sean los mismos menos el nuevo en v2
los titulares son los mismos
el autorizado ya esta en v1 (no estaria agregando a nadie)
*/
/*No tendria q generar una instancia donde los autos posean distintas patentes pero lo genera*/
run casoNoExito4Patente{some disj v1,v2 : Vehiculo, p : Persona | v1.placa != v2.placa and agregarAutorizado[v1, v2, p]}

/*No tendria q generar una instancia donde los autos sean de distinto tipo*/
run casoNoExito5Tipo{some disj v1,v2 : Vehiculo, p : Persona | v1 in Proveeduria and v2 in Gerencial and agregarAutorizado[v1, v2, p]}

/*No tendria q generar una instancia donde haya distintos titulares y no lo genera, esta bien*/
run CasoNoExito6{some disj v1,v2 : Vehiculo, p : Persona | #v1.titulares != #v2.titulares and  agregarAutorizado[v1, v2, p]}

/*para confirmar el caso anterior, genero una instancia donde si haya misma cantidad de titulares*/
run CasoExito3{some disj v1,v2: Vehiculo, p: Persona |  #v1.titulares = #v2.titulares and  agregarAutorizado[v1, v2, p]}

/*Tendria q generar una instancia donde los autorizados sean los mismos menos el nuevo en v2 */
run casoExito4{some disj v1,v2: Vehiculo, p: Persona | v1.autorizados = v2.autorizados - p and agregarAutorizado[v1, v2, p]}

/*el autorizado ya estaba en v1, no tendria q permitirmelo, sin embargo genera instancia*/
run CasoNoExito7{some disj v1,v2: Vehiculo, p : Persona | p in v1.autorizados and agregarAutorizado[v1, v2, p]}


----------------------------------------------------------------------------------------------------------
/*c)*/
pred agregarAutorizadoCorregido[v1, v2: Vehiculo, p: Persona] {
	(one p.carnet) and
	(#v1.autorizados < #v1.titulares) and
	(p in v2.autorizados) and
	(v2.titulares = v1.titulares) and

	p !in v1.autorizados and 
	(v1 in Proveeduria and v2 in Proveeduria) and
	(v1.placa = v2.placa) and 
	(v1.autorizados = v2.autorizados - p)  
	
}
------------------------------------------------------------------------------------------------------
//d) obtener el conjunto de personas que poseen al menos 18 a˜nos
//no tienen carnet de conducir y son titulares alg´un veh´ıculo comercial o gerencial.

fun obtenerPersonas [] : set Persona{{
	p : Persona | p in Mayoria18 and p.carnet = none and (p in Comercial.titulares or p in Gerencial.titulares)

}}


run testFuncion { some p : Persona |  
	p in Mayoria18 and p.carnet = none and  (p in Comercial.titulares or p in Gerencial.titulares)
}

