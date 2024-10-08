
 abstract sig Chocolate { 
 formato: FormatoChoco 
 }
 sig ChocoBlanco, ChocoLeche, ChocoSemiAmargo extends Chocolate {}
 
abstract sig FormatoChoco {}

one sig Tableta, Relleno extends FormatoChoco { }

abstract sig Caja { 
 tam: Tamanio,
 chocolates: some Chocolate
}
 abstract sig Tamanio {}
 
one sig Chico, Mediano, Grande extends Tamanio {}
 
fact { all c: Caja | (c.tam = Chico) implies (#c.chocolates =<3) }
 
fact { all c: Caja | (c.tam = Mediano) implies (#c.chocolates >=4 and #c.chocolates =<5) }
 
fact { all c: Caja | (c.tam = Grande) implies (#c.chocolates >=6 and #c.chocolates =<7) }
 
fact { no disj c1, c2: Caja, c: Chocolate | (c in c1.chocolates) and (c in c2.chocolates) }

fact { all c:Caja |
				( (c.chocolates in ChocoBlanco ) or (c.chocolates in ChocoLeche) or (c.chocolates in ChocoSemiAmargo) )or
				( (c.chocolates.formato in Tableta ) or (c.chocolates.formato in Relleno) )
			
}
fact {all c:Caja | (c.tam in Grande) implies ((#(c.chocolates & formato.Relleno  )<4) ) }


// Predicado dado en el enunciado 
// reemplazar un chocolate de una caja por otro chocolate. Esta accion es  posible siempre y cuando la caja original 
// posea al menos un chocolate relleno y a lo sumo un chocolate blanco
 pred reemplazarChocolate[ch1, ch2: Chocolate, ca1, ca2: Caja]{
 (ch2 ! in ca1.chocolates) and
 (#(ca1.chocolates & formato.Relleno) >=1) and
 (ch2 in ca2.chocolates)
 }



/////////////////////////////////////////////////////////////////////////////// Lo que pedian en el parcial como validacion /////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////

//  ch1 y ch2 pueden ser el mismo chocolate:
run Ch1Ch2MismoChocolate{some ch1, ch2: Chocolate, ca1, ca2: Caja | (ch1 = ch2 ) and reemplazarChocolate[ch1,ch2,ca1,ca2]} 

// ch1 no estaba en ca1
run Ch1NoEstaCa1 {some ch1, ch2: Chocolate, ca1, ca2: Caja | (ch1 !in ca1.chocolates) and reemplazarChocolate[ch1,ch2,ca1,ca2]}

// ch1 está en ca2 
run Ch1EstaCa2 {some ch1, ch2: Chocolate, ca1, ca2: Caja | (ch1 in ca2.chocolates) and reemplazarChocolate[ch1,ch2,ca1,ca2]}

// ca1 tiene un chocolate que no está en ca2 (distinto de ch1 y ch2)
run Ca1TieneChocolateNoEstaEnCa2 { some ch1, ch2: Chocolate, ca1, ca2: Caja | reemplazarChocolate[ch1,ch2,ca1,ca2]  and  (ca1.chocolates-ch1 != ca2.chocolates-ch2 ) }

// ca1 posee más de 1 chocolate blanco 
run Ca1Mas2ChocoBlanco { some ch1, ch2: Chocolate, ca1, ca2: Caja |  reemplazarChocolate[ch1,ch2,ca1,ca2] and #(ca1.chocolates & ChocoBlanco)>=2 }

// ca1 y ca2 tienen distinto tamaño
run Ca1yCa2DistintosTamano { some ch1, ch2: Chocolate, ca1, ca2: Caja | reemplazarChocolate[ch1,ch2,ca1,ca2] and (ca1.tam !in ca2.tam)  }

// ch1 está en ca2 
run Ch1EstaCa2 {some ch1, ch2: Chocolate, ca1, ca2: Caja | (ch1 in ca2.chocolates) and reemplazarChocolate[ch1,ch2,ca1,ca2]}		
			
// ca2 tiene chocolates que no estaban en ca1 (distintos de ch2)
run Ca2TieneChocolatesNoEstabaCa1 { some ch1, ch2: Chocolate, ca1, ca2: Caja | reemplazarChocolate[ch1,ch2,ca1,ca2] and (ca2.chocolates !in (ca1.chocolates + ch2))  }


/////////////////////////////////////////////////////////////////////////////////////// DATOS EXTRA PARA VER ERROR O COMO HACER LAS COSAS///////////////////////////////////////////////////////////////////////////////


// Ambos son inecesarios e irrelevantes ya que escriben textual lo que se encuentra en los facts de los tamanos, no puedo poner textual lo mismo de lo que esta escrito en un fact o pred
run A{ some ch1, ch2: Chocolate, ca1, ca2: Caja |  reemplazarChocolate[ch1,ch2,ca1,ca2]  and (#(ca1.chocolates)=7)}for 8
run B{ some ch1, ch2: Chocolate, ca1, ca2: Caja |  reemplazarChocolate[ch1,ch2,ca1,ca2]  and (#(ca1.chocolates)=3)}for 4

// El error es que aca unicamente necesitaba escribir #(ca1.chocolates & ChocoBlanco)=2  que era lo que necesitaba ver, ya que en el enunciado me decia a lo sumo (0 o 1) 
// un chocolate blanco y de relleno es inecesario anotarlo. 
run C{ some ch1, ch2: Chocolate, ca1, ca2: Caja |  reemplazarChocolate[ch1,ch2,ca1,ca2] and (#(ca1.chocolates & formato.Relleno  )>=1)and #(ca1.chocolates & ChocoBlanco)=2 }

//Devuelta #(ca1.chocolates & formato.Relleno  )= 0)  es practicamente lo mismo que  (#(ca1.chocolates & formato.Relleno) >=1) que se encuentra en el pred, por eso es poco abarcativo
run D{some ch1, ch2: Chocolate, ca1, ca2: Caja |  reemplazarChocolate[ch1,ch2,ca1,ca2] and (#(ca1.chocolates & formato.Relleno  )= 0) }

// poniendolo asi puedo tengo que ponerlo (ca1.chocolates-ch1 !in ca2.chocolates-ch2 )and(ca2.chocolates-ch2 !in ca1.chocolates-ch1) para hacer el ida y vuelta sino uso el != para que sea para ambas partes
// (ca1.chocolates-ch1 !in ca2.chocolates-ch2 )and(ca2.chocolates-ch2 !in ca1.chocolates-ch1) es IGUAL A (ca1.chocolates-ch1 != ca2.chocolates-ch2 )
run Opcion2 { some ch1, ch2: Chocolate, ca1, ca2: Caja | reemplazarChocolate[ch1,ch2,ca1,ca2] and (ca1.chocolates-ch1 !in ca2.chocolates-ch2 )and(ca2.chocolates-ch2 !in ca1.chocolates-ch1) }

																				



