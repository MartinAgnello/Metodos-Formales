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
//fact {all c: Caja | no disj p1, p2: c.packs | some (p1.cervezas & p2.cervezas)}

// Las cervezas Ale se fermentan a temperatura alta, mientras que las Lager se fermentan a temperatura baja.

fact { all c:Ale | c.temperatura=Alta }
fact { all c: Lager | c.temperatura = Baja}


// Las cervezas dentro del mismo pack son de la misma variedad o poseen la misma tonalidad.
// Variedad Weisse, IPA, Porter, Pilser, Bock y tonalidad: clara, oscura, intermedia


fact { all p:Pack | ( (p.cervezas in IPA ) or (p.cervezas in Weisse ) or (p.cervezas in Porter ) or (p.cervezas in Pilsner ) or (p.cervezas in Bock ) ) or 
				(  ( p.cervezas in (Clara-Oscura) ) or
				   ( (p.cervezas in Clara) and (p.cervezas in Oscura) ) or
				   (  p.cervezas in (Oscura-Clara) )  	

				) 	 	
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

pred cambiarCervezaV2[c1, c2: Cerveza, p1, p2: Pack] {
	--Precondicion
	 c1 in p1.cervezas and
 	c2 !in p1.cervezas and 
	//que no sean 
	c1!=c2 and
	//p1 y p1 no pueden estar en una caja
	(some c: Caja | (p1 !in c.packs  ) and (p2 !in c.packs) ) and 
	
	--Marco 
	//Las cervezas de p1 y de p2 tienen que ser las mismas (excepto c1 y c2)
	(p1.cervezas - c1) = (p2.cervezas - c2) and
	
      --PostCondicion
	// c2 tiene que estan en las cervezas de p2 
 	c2 in p2.cervezas and
	// c1 no tiene que estar en las cervezas de p2 
        c1 !in p2.cervezas and
	// p2 tiene que ser las cervezas de p1 con c2 y sin c1(remplazada) 
	p2.cervezas  = p1.cervezas + c2 - c1


}


// 7 DE EXITO

// En este caso al cambiar de igual tipo me pasa que se puede realizar pilser y weisse son de la misma tonalidad por lo tanto me retorna una instancia,
// lo cual hace al predicado verdadero por eso se determina como un caso de exito. 

run CambiarPilsneWeisse{some c1,c2:Cerveza, p1,p2: Pack | cambiarCervezaV2[c1, c2, p1, p2] and (c1 in Pilsner) and (c2 in Weisse) }for 7

run CambiarWeissePilser {some c1,c2:Cerveza, p1,p2: Pack | cambiarCervezaV2[c1, c2, p1, p2] and (c1 in Weisse) and (c2 in Pilsner) }for 7

run CambiarBockIPA {some c1,c2:Cerveza, p1,p2: Pack | cambiarCervezaV2[c1, c2, p1, p2] and (c1 in Bock) and (c2 in IPA) } 

run CambiarIPABock {some c1,c2:Cerveza, p1,p2: Pack | cambiarCervezaV2[c1, c2, p1, p2] and (c1 in IPA) and (c2 in Bock) }




// 7 DE NO EXITO

// no tengo tiempo pero basicamente lo que hacen todos es probar dos tipos distintos de cerveza y al intentar hacerlo no me retorna una instancia, esto pasa
// por los fact de restricciones anteriores (tonalidad )

run CambiarWeissePorter{some c1,c2:Cerveza, p1,p2: Pack | cambiarCervezaV2[c1, c2, p1, p2] and (c1 in Weisse) and (c2 in Porter) }

run CambiarPilsnerPorter {some c1,c2:Cerveza, p1,p2: Pack | cambiarCervezaV2[c1, c2, p1, p2] and (c1 in Pilsner) and (c2 in Porter) }

run CambiarIPAPorter{some c1,c2:Cerveza, p1,p2: Pack | cambiarCervezaV2[c1, c2, p1, p2] and (c1 in IPA) and (c2 in Porter) }

run CambiarBockPorter{some c1,c2:Cerveza, p1,p2: Pack | cambiarCervezaV2[c1, c2, p1, p2] and (c1 in Bock) and (c2 in Porter) }

run CambiarWeisseIPA{some c1,c2:Cerveza, p1,p2: Pack | cambiarCervezaV2[c1, c2, p1, p2] and (c1 in Weisse) and (c2 in IPA) }

run CambiarWeisseBock{some c1,c2:Cerveza, p1,p2: Pack | cambiarCervezaV2[c1, c2, p1, p2] and (c1 in Weisse) and (c2 in Bock) }

run CambiarIPAPilsner{some c1,c2:Cerveza, p1,p2: Pack | cambiarCervezaV2[c1, c2, p1, p2] and (c1 in IPA) and (c2 in Pilsner) }




















