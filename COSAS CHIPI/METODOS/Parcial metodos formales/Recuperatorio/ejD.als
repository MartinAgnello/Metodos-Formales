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
Si el pack a anadir posee 2 cervezas, ninguna cerveza del pack a ser anadido debe tener la
misma tonalidad que alguna cerveza de los packs restantes de la caja. Por otra parte, si el
pack a anadir posee 3 cervezas, ninguna cerveza del pack a ser anadido debe ser de la misma
variedad que alguna cerveza de los packs restantes de la caja.


*/


pred agregarPack[p: Pack, c1, c2: Caja]{ 

--Precondicion
 // pack c no esta incluido en c1
 (p !in c1.packs) and 
 // p tiene que estar en c2
 (p in c2.packs) and
 // chequeo que los packs de c1 esten en c2
 (c1.packs in c2.packs ) and
 // c1 no tenga mas de 5 packs
  (#c1.packs=< 5) and





// si el pack posee dos cervezas, no debe poseer (esas cervezas) la misma tonalidad que las de la caja 
 ( (#p.cervezas=2) implies ( ( (c1.packs.cervezas in Oscura) implies (p.cervezas !in Oscura) ) and 
				       ( (c1.packs.cervezas in Clara) implies (p.cervezas !in Clara) ) )

																		
)and
// si el pack posee tres cervezas , no debe tener la misma variedad que las que estan en la caja

(  (#p.cervezas=3)  implies (  ( (c1.packs.cervezas in IPA) implies (p.cervezas !in IPA)) and  
					      ((c1.packs.cervezas in Bock) implies (p.cervezas !in Bock)) and
					      ((c1.packs.cervezas in Weisse) implies (p.cervezas !in Weisse)) and
					       ((c1.packs.cervezas in Pilsner ) implies (p.cervezas !in Pilsner )) and
					       ((c1.packs.cervezas in Porter) implies  (p.cervezas !in Porter)) 


)
)and



--Postcondicion and Marco
// la caja c2 tiene que tener los packs de c1 mas el pack agregado
c2.packs = c1.packs + p

}




--Caso de NO Exito
// Pruebo que se puedan agregar un pack donde el pack tiene una porter y una weisee (al ser las dos de diferente tonalidad), no me devuelve instancia.
// Por lo tanto es de no exito porque el predicado se me hace falso.
run CambiandoSinExito1{ some c1,c2: Caja, p: Pack | agregarPack[p, c1, c2] and  (#p.cervezas=2) and #(p.cervezas & Porter)=1 and #(p.cervezas & Weisse)=1   }for 8

// Pruebo que se puedan agregar un pack donde el pack tiene una porter y una Pilsner (al ser las dos de diferente tonalidad), no me devuelve instancia.
run CambiandoSinExito2{ some c1,c2: Caja, p: Pack | agregarPack[p, c1, c2] and  (#p.cervezas=2) and #(p.cervezas & Porter)=1 and #(p.cervezas & Pilsner )=1   }for 8

//Pruebo si en un pack de 3 cervezas puedo tener una oscura y una clara y como se ve claramente no se puede, por eso no retorna una instancia 
run CambiandoSinExito3 { some c1,c2: Caja, p: Pack | agregarPack[p, c1, c2] and  (#p.cervezas=3) and (#(p.cervezas & Oscura)=1 or #(p.cervezas & Clara )=1)  }for 8



-- Caso de EXITO 
// como vemos es un caso de exito, ya que me devuelve una instancia. Lo que le pedi es que el pack tenga una Pilsner y una Weisse lo cual ambas son de la misma tonalidad
run CambiandoExito1{ some c1,c2: Caja, p: Pack | agregarPack[p, c1, c2] and  (#p.cervezas=2) and #(p.cervezas & Pilsner)=1 and #(p.cervezas & Weisse)=1   }for 8

// Pruebo con un pack con dos cervezas Porter cambiar y como son de la misma tonalidad devulve una instancia.
run CambiandoExito2{ some c1,c2: Caja, p: Pack | agregarPack[p, c1, c2] and  (#p.cervezas=2) and #(p.cervezas & Porter)=2  }for 8


// Pruebo un pack con tres cervezas Claras y me retorna una instancia ya que me puede dar cervezas o Weisse o Pilser
run CambiandoExito3{ some c1,c2: Caja, p: Pack | agregarPack[p, c1, c2] and  (#p.cervezas=3) and #(p.cervezas & Clara)=3  }for 8

// Pruebo un pack con tres cervezas Claras y me retorna una instancia ya que me puede dar cervezas Tipo Porter
run CambiandoExito3{ some c1,c2: Caja, p: Pack | agregarPack[p, c1, c2] and  (#p.cervezas=3) and #(p.cervezas & Oscura)=3  }for 8


// Pruebo un pack con tres cervezas Claras y me retorna una instancia ya que me puede dar cervezas o Weisse o Pilser
run CambiandoExito3{ some c1,c2: Caja, p: Pack | agregarPack[p, c1, c2] and  (#p.cervezas=3) and #(p.cervezas & Clara)=3  }for 8




















































