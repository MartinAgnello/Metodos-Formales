abstract sig Cerveza {
temperatura: one Fermentacion 
}

abstract sig Ale, Lager extends Cerveza {}

sig Clara, Oscura in Cerveza {}

sig Weisse, IPA, Porter extends Ale {}

sig Pilsner, Bock extends Lager {}

abstract sig Fermentacion {}

one sig Alta, Baja extends Fermentacion {}

sig Caja { packs: some Pack }

sig Pack { cervezas: some Cerveza }

fact {all c: Cerveza | (c in (Clara-Oscura)) or (c in (Oscura-Clara)) or (c in (Clara & Oscura))}

fact {all p: Pack | (#p.cervezas = 2) or (#p.cervezas = 3)}

fact {all c: Caja | (#c.packs.cervezas >= 2) and (#c.packs.cervezas =< 6)}

// Los packs de una misma caja no comparten cervezas
fact {all c: Caja | no disj p1, p2: c.packs | some (p1.cervezas & p2.cervezas)}


// Las cervezas Ale se fermentan a temperatura alta, mientras que las Lager se fermentan a temperatura baja.

fact { all c:Ale | c.temperatura=Alta }
fact { all c: Lager | c.temperatura = Baja}


// Las cervezas dentro del mismo pack son de la misma variedad o poseen la misma tonalidad.
// Variedad Weisse, IPA, Porter, Pilser, Bock y tonalidad: clara, oscura, intermedia

fact { all p:Pack | ( (p.cervezas in IPA )or(p.cervezas in Weisse )or(p.cervezas in Porter )or(p.cervezas in Pilsner )or(p.cervezas in Bock ) ) or
			      ( (p.cervezas in Clara ) or (p.cervezas in Oscura) or ( (p.cervezas in Clara)and(p.cervezas in Oscura)) )		
 }

//La cerveza Pilser es clara
fact {all c:Pilsner | (c in Clara) and (c ! in Oscura) }
//La cerveza Porter es Oscura 
fact {all c:Porter | (c ! in Clara) and (c in Oscura) }
//La cerveza Weisse es clara
fact {all c:Weisse | (c in Clara) and (c ! in Oscura) }
//La cerveza IPA es clara y oscura(intermedio)
fact {all c:IPA | (c in Clara) and (c  in Oscura) }
//La cerveza Bock es clara y oscura (intermedio)
fact {all c:Bock | (c in Clara) and (c  in Oscura) }


/*
el cual modela el comportamiento de cambiar una cerveza de un pack por otra cerveza que este fuera del pack.
Esta accion es posible siempre y cuando el pack no este en una caja.

*/
pred cambiarCerveza[c1, c2: Cerveza, p1, p2: Pack]{
(some (c2 & p1.cervezas)) and
(c2 in p2.cervezas)
}


------------------------------------------------------- Validacion ----------------------------------------------------------------------------------------


// Cerveza C1 y Cerveza c2 puede ser la misma, retorna una instancia haciendo verdadero al predicado
run C1C2MismaCerveza {some c1, c2 : Cerveza, p1,p2 : Pack | (c1=c2) and cambiarCerveza[c1,c2,p1,p2] }

// Cerveza C1 no esta en el Pack p1, retorna una instancia haciendo verdadero al predicado
run C1NoEstaenP1{some c1, c2 : Cerveza, p1,p2 : Pack |  cambiarCerveza[c1,c2,p1,p2] and (c1 !in p1.cervezas)}

// Cerveza C1 esta en el Pack p1, retorna una instancia haciendo verdadero al predicado
run C1EstaEnP2{some c1, c2 : Cerveza, p1,p2 : Pack |  cambiarCerveza[c1,c2,p1,p2] and (c1 in p1.cervezas)}

// p1 tiene una cerveza que no esta e p2 (distinto de c1 y c2), devuelve una instancia   
run P1TieneCervezaNoEstaEnP2{some c1, c2 : Cerveza, p1,p2 : Pack |  cambiarCerveza[c1,c2,p1,p2] and (p1.cervezas-c1 != p2.cervezas-c2) }
									
// p1 ni p2 esta en una caja 
run P1P2EstanEnCaja {some c1, c2 : Cerveza, p1,p2 : Pack, caja: Caja |  cambiarCerveza[c1,c2,p1,p2] and ( (p1 in caja.packs)or(p2 in caja.packs) )  }

// C1 esta en p2
run C1EstaEnP2 {some c1, c2 : Cerveza, p1,p2 : Pack |  cambiarCerveza[c1,c2,p1,p2] and (c1 in p2.cervezas) }

// p2 tiene cervezas que no estaban en p1 (distinto de c2)
run P2TieneCervezasNoEstabanEnP1 {some c1, c2 : Cerveza, p1,p2 : Pack |  cambiarCerveza[c1,c2,p1,p2] and (p2.cervezas !in (p1.cervezas + c2)) }





























