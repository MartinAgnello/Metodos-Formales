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

//-------------------------------------------------------------------------------------------------------------------------------------------
//b)
/*
Incorpore al modelo el siguiente predicado, el cual modela el comportamiento de a˜nadir una
persona al conjunto de personas autorizadas a manejar un veh´ıculo de proveedur´ıa. Esta acci´on
es posible siempre y cuando la persona posea licencia de conducir y la cantidad original de
personas autorizadas a manejar el veh´ıculo no supere a la cantidad de titulares del mismo:

Restricciones: 
los vehiculos sean de proveduria
la persona tenga licencia de conducion
antidad original de personas autorizadas a manejar el vehiculo no supere a la cantidad de titulares del mismo
*/
//chequeos relacionados al problema (el enunciado)
pred agregarAutorizado[v1, v2: Vehiculo, p: Persona] {
	(one p.carnet) and
	(#v1.autorizados > #v1.titulares) and
	(p in v2.autorizados) and
	(v2.titulares = v1.titulares)
}

//casos de prueba:

//los vehiculos sean de proveduria
run CasoNoExito1 { some disj v1, v2 : Vehiculo, p : Persona | v1 in Comercial and v2 in Comercial and
				agregarAutorizado[v1,v2,p]
	
}
//se puede crear una instancia donde no es proveduria por lo tanto el predicado falla para esta restriccion

run CasoNoExito2 { some disj v1, v2 : Vehiculo, p : Persona | p.carnet = none and
				agregarAutorizado[v1,v2,p]		
}

run CasoExito2 { some disj v1, v2 : Vehiculo, p : Persona | p.carnet != none and
				agregarAutorizado[v1,v2,p]		
}
//funciona god

//la persona tenga licencia de conducion
run CasoNoExito3 { some disj v1, v2 : Vehiculo, p : Persona | #v1.autorizados > #v1.titulares and
	agregarAutorizado[v1,v2,p]
}

//cantidad original de personas autorizadas a manejar el vehiculo no supere a la cantidad de titulares del mismo
run CasoExito3 { some disj v1, v2 : Vehiculo, p : Persona | #v1.autorizados < #v1.titulares and
	agregarAutorizado[v1,v2,p]
}
//no puedo generar instancias donde los autorizados sean menores a los titulares

//************************************************************************************
/*
chequeos logicos:
los titulares sean los mismos
los autorizados sean los mismos menos el nuevo
la patente sea la misma
los autos sean del mismo tipo
la persona a agregar no este entre los autorizados de v1
*/
//los titulares sean los mismos
run CasoNoExito4 { some disj v1, v2 : Vehiculo, p : Persona | v1.titulares != v2.titulares and
			agregarAutorizado[v1,v2,p]		
}
run CasoExito4 { some disj v1, v2 : Vehiculo, p : Persona | v1.titulares = v2.titulares and
			agregarAutorizado[v1,v2,p]		
}
//funciona god

//los autorizados sean los mismos menos el nuevo
run CasoNoExito5 {some disj v1, v2 : Vehiculo, p : Persona | v1.autorizados != v2.autorizados - p and
			agregarAutorizado[v1,v2,p]
}
//no preserva a los autorizados, puede existir un caso donde los autorizados del auto 1 desaparecen

//la patente sea la misma
run CasoNoExito6 { some disj v1, v2 : Vehiculo, p : Persona | v1.placa != v2.placa and
			agregarAutorizado[v1,v2,p]		
}
//los autos puden cambiar de patente

//los autos sean del mismo tipo
run CasoNoExito7 { some disj v1, v2 : Vehiculo, p : Persona | v1 in Comercial and v2 in Gerencial and
			agregarAutorizado[v1,v2,p]		
}
//los autos cambian de tipo

//la persona a agregar no este entre los autorizados de v1
run CasoNoExito8 { some disj v1, v2 : Vehiculo, p : Persona | p in v1.autorizados and
			agregarAutorizado[v1,v2,p]		
}
//la persona p ya puede ser un autoriado

//-----------------------------------------------------------------------------------------------------------------------------------
//c)

pred agregarAutorizadoCorregido[v1, v2: Vehiculo, p: Persona] {
	(one p.carnet) and
	(#v1.autorizados < #v1.titulares) and
	(p in v2.autorizados) and
	(v2.titulares = v1.titulares)

	v1 in Proveeduria and
	v2 in Proveeduria and
	v1.autorizados = v2.autorizados - p
	p not in v1.autorizados and 
	v1.placa = v2.placa
	
}

//---------------------------------------------------------------------------------------------------------------------------------
//d)
fun obtenerPersona [] : set Persona {{
	p : Persona | p in Mayoria18 and p.carnet = none and (p in Comercial.titulares or p in Gerencial.titulares)
}}

run testFuncion { some p : Persona |  
	p in Mayoria18 and p.carnet = none and  (p in Comercial.titulares or p in Gerencial.titulares)
}

//--------------------------------------------------------------------------------------------------------------------------------
//e)
/*
luego del traspaso, el veh´ıculo deber´a contar con al menos una persona autorizada para manejarlo
la persona no debe ser titular de un veh´ıculo de distinto tipo al veh´ıculo para el cual se est´a realizando el traspaso. 
*/

pred autorizadoATitular[v1, v2: Vehiculo, p: Persona]{
	//precondiciones
	p in v1.autorizados and
	p not in v1.titulares and
	
	//invariantes
	v1.placa = v2.placa and
	mismoTipo[v1,v2] and

	//postcondiciones
	v1.autorizados = v2.autorizados + p and
	v1.titulares = v2.titulares - p and
	p in v2.titulares and
	p not in v2.autorizados and
	#v2.autorizados >= 1
}

pred mismoTipo[v1,v2:Vehiculo] {
	(v1 in Proveeduria and v2 in Proveeduria) or
	(v1 in Comercial and v2 in Comercial) or
	(v1 in Gerencial and v2 in Gerencial)
}



