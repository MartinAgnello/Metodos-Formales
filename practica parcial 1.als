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

/*No hay vehiculos que no pertenezcan a Provencial, Comercial, Gerencial*/
fact {no Vehiculo - Proveeduria - Comercial - Gerencial}

/*Los vehıculos con patente poseen entre uno y dos titulares*/
fact {all v: Vehiculo | (some v.placa) implies (some v.titulares and #v.titulares < 3)}

/*No debe existir ningún vehículo q tenga al menos 1 persona que sea simultáneamente titular y autorizada.*/
fact {no v: Vehiculo | some (v.titulares & v.autorizados)}

/*No debe existir vehiculo tq no tenga placa y que tenga algun titular o autorizado*/
fact {no v: Vehiculo | (no v.placa) and ((some v.titulares) or (some v.autorizados))}

/*No existen 2 personas distintas q compartan id*/
fact {no disj p1, p2: Persona | (p1.id = p2.id)}

/*No existe persona que no perteneza a Menor, Mayoria16, Mayoria18 */
fact {no Persona - Menor - Mayoria16 - Mayoria18}

fact {no Menor & Mayoria16}

fact {no Menor & Mayoria18}

/*Los mayores de 18 son mayores de 16*/
fact {Mayoria18 in Mayoria16}

/*Toda persona que sea titular de algún vehículo debe pertenecer al conjunto Mayoria18
   titulares.p es la consulta inversa: busca todos los vehículos en los que p aparece como titular.*/
fact {all p: Persona | (some titulares.p) implies (p in Mayoria18)}

fact {all p: Persona | (some autorizados.p) implies (p in Mayoria16)}

fact {all p: Persona | (some p.carnet) implies (p in Mayoria16)}

fact {all vg: Gerencial | lone vg.titulares}

fact {all vp: Proveeduria | #(vp.autorizados) < 4}

/*No existen 2 personas distintas que posean el mismo carnet*/
fact {no disj p1, p2: Persona | (some p1.carnet) and (some p2.carnet) and
					(p1.carnet = p2.carnet)}

fact {no disj v1, v2: Vehiculo | (some v1.placa) and (some v2.placa) and
					(v1.placa = v2.placa)}
-----------------------------------------------------------------------------------------------------------------
/* modela el comportamiento de añadir una persona al conjunto de personas autorizadas a manejar un 
vehıculo de proveedurıa. Esta accion es posible siempre y cuando la persona posea licencia de conducir y la 
cantidad original de personas autorizadas a manejar el vehıculo no supere a la cantidad de titulares del mismo:
*/
/*
pred agregarAutorizado[v1, v2: Vehiculo, p: Persona] {
	(one p.carnet) and
	(#v1.autorizados > #v1.titulares) and
	(p in v2.autorizados) and
	(v2.titulares = v1.titulares)
}*/

/*Caso de no exito: agrego una persona autorizada a un vehiculo que no es de proveeduria, no tendria que
generar instancia pero la genera igualmente*/

run VehiculoNoEsDeProveeduria{ some disj v1,v2 : Vehiculo, p: Persona | Vehiculo !in Proveeduria and 
													agregarAutorizado[v1,v2,p]}

/*Caso de no exito: no agrego a un persona nueva, no tendria q generar instancia y la genera*/
run NoAgregoPersonaNueva{ some disj v1,v2 : Vehiculo, p: Persona | p in v1.autorizados and agregarAutorizado[v1,v2,p]}


/*Caso de exito: Los autorizados superan la cantidad de titulares, no tendria q generar instancia y la genera*/
run MasAutorizadosQueTitulares{ some disj v1,v2 : Vehiculo, p: Persona | #v1.autorizados > #v1.titulares and agregarAutorizado[v1,v2,p]}

/*Caso de exito: La persona a agregar tiene carnet*/
run PersonaConCarnet { some disj v1, v2 : Vehiculo, p : Persona | p.carnet != none and
				agregarAutorizado[v1,v2,p]		
} for 7

/*Caso de no exito: La persona a agregar tiene carnet*/
run PersonaSinCarnet { some disj v1, v2 : Vehiculo, p : Persona | p.carnet = none and
				agregarAutorizado[v1,v2,p]		
}

----------------------
/*chequeos logicos:
La persona no se encuentra en v1
personas autorizadas <= titulares 
autorizados v1 = autorizados v2 + p
el auto es el mismo, o sea tiene misma placa y mismo tipo
*/

/*Caso no exito: los autorizados son distintos*/
run AutorizadosDistintos { some disj v1, v2 : Vehiculo, p : Persona | #v1.autorizados > #(v2.autorizados + p) and
												     agregarAutorizado[v1,v2,p]}
/*Caso no exito: los vehiculos tienen distinta patente*/
run PlacasDist { some disj v1, v2 : Vehiculo, p : Persona | v1.placa != v2.placa and agregarAutorizado[v1,v2,p]}

-------------------------------------------------------------------
/*c*/
pred agregarAutorizado[v1, v2: Vehiculo, p: Persona] {
	(v1 in Proveeduria and v2 in Proveeduria) and
	(one p.carnet) and
	(p !in v1.autorizados) and 
	(#v1.autorizados <= #v1.titulares) and
	(p in v2.autorizados) and
	(v2.titulares = v1.titulares) and
	(v2.autorizados = v1.autorizados + p) and
	(v1.placa = v2.placa)
}
---------------------------------------------------------------------
//d) obtener el conjunto de personas que poseen al menos 18 a˜nos
//no tienen carnet de conducir y son titulares alg´un veh´ıculo comercial o gerencial.
fun obtenerPersonas [] : set Persona{{ p: Persona | p in Mayoria18 and #p.carnet = 0 and 
									        (p in Comercial.titulares or p in Gerencial.titulares) }}

run testFuncion{ some p : Persona |  #p.carnet = 0 and p in Comercial.titulares }
