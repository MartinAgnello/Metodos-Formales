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


fact { all p:Pack | ( (p.cervezas in IPA ) or (p.cervezas in Weisse ) or (p.cervezas in Porter ) or (p.cervezas in Pilsner ) or (p.cervezas in Bock ) ) or 
				(  ( p.cervezas in (Clara-Oscura) ) or
				   ( (p.cervezas in Clara) and (p.cervezas in Oscura) ) or
				   (  p.cervezas in (Oscura-Clara) )  	

				) 	 	
 }


// Las cervezas Weisse y Pilsner son claras, mientras que las IPA y Bock son intermedias, y las Porter son oscuras.


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




------------------------------------- CHEQUEO PRIMER FACT--------------------------------------------------------
// chequeo que si la cerveza es tipo ale este en tamperatura baja y  no retorna una instancia, ya que no deberia de pasar porque solo fermenta en tempertura alta 
run CervezaAleTempBaja{ some c: Cerveza | (c in Ale) and (c.temperatura in Baja) }
// chequeo que si la cerveza es tipo ale este en tamperatura alta y retorna una instancia 
run CervezaAleTempAlta{ some c: Cerveza | (c in Ale) and (c.temperatura in Alta) }

// chequeo que la cerveza lager fermente en temperatura alta, como esto no puede pasar, no retorna una instancia
run CervezaAleTempAlta{ some c: Cerveza | (c in Lager) and (c.temperatura in Alta) }
// chequeo que la cerveza lager fermente en temperatura baja, retorna una instancia 
run CervezaAleTempAlta{ some c: Cerveza | (c in Lager) and (c.temperatura in Baja) }


-------------------------------------- CHEQUEO SEGUNDO FACT----------------------------------------------------
// hago que halla un paquete con cervezas tipo y no retonra nada, porque no deberia de pasar
run MismoVariedadDistintoTonalidad {some p:Pack | (p.cervezas in Ale)and (p.cervezas in IPA) and (p.cervezas in Clara) }

// trato de que lager y weiise sean oscura y esto no puede pasar por eso no retorna una instancia 
run MismoVariedadDistintoTonalidad2 {some p: Pack | (p.cervezas in Lager)and (p.cervezas in Weisse) and (p.cervezas in Oscura) }


-------------------------------Chequeo Tercer fact---------------------------------------------------

// No devuelve nada porque Weisse o Pilsner no puede ser oscura
run WeissePilserOscura { all c:Cerveza | ( (c in Weisse)or(c in Pilsner) ) and (c in Oscura)  }
// Devuelve una instancia porque Weisse Pilsner tiene que ser de tonalidad clara
run WeissePilserClara{ some c:Cerveza | ( (c in Weisse)or(c in Pilsner) ) and (c in Clara)  }
// No deuvle una instancia porque Weise o plnser tiene que ser de tonalidad Solo Clara, no clara y oscura
run WeissePilserClara{ some c:Cerveza | ( (c in Weisse)or(c in Pilsner) ) and ((c in Clara)and (c in Oscura))  }

// Devulve una instancia con porter con tonalidad Oscura
run PorterOscura { some c:Cerveza | ( (c in Porter) ) and (c in Oscura)  }
// No devuelve una instancia con Porter con tanaldad clara y no oscura, ya que tiene que ser solo oscura
run PorterClara  { some c:Cerveza | ( (c in Porter) ) and (c in Clara) }
// No devuelve una instancia con Porter con tanaldad clara y  oscura, ya que tiene que ser solo oscura
run PorterIntermedia { some c:Cerveza | ( (c in Porter) ) and (c in Clara)and(c in Oscura)  }


// Ipa solo Clara, no devuelve instancia
run IPAClaraSolo { some c:Cerveza | ( (c in IPA) or (c in Bock) ) and (c in Clara)and(c !in Oscura) } 
// Ipa solo Oscura, no vuelve instancia 
run IPAOscuraSolo { some c:Cerveza | ( (c in IPA)or (c in Bock) ) and (c !in Clara)and(c in Oscura)  } 
// Ipa Intermedia, si devulve instancia ya que tiene que ipa tener oscuro y claro 
run IPAIntermedio{ some c:Cerveza | ( (c in IPA)or (c in Bock) ) and (c in Clara)and(c in Oscura)  } 








