
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
 
//fact { no disj c1, c2: Caja, c: Chocolate | (c in c1.chocolates) and (c in c2.chocolates) }

----------------------   INCISO A -----------------------------------------------------------------------------

// Los chocolates dentro de una misma caja son del mismo tipo o poseen el mismo formato.
// Formato es de Tableta o Relleno, tipo es ChocoBlanco, ChocoLeche, ChocoSemiAmargo, 
fact { all c:Caja | 
				// Mismo tipo
				( (c.chocolates in ChocoBlanco ) or (c.chocolates in ChocoLeche) or (c.chocolates in ChocoSemiAmargo) )or
				// Mismo FormatoChoco
				( (c.chocolates.formato in Tableta ) or (c.chocolates.formato in Relleno) )
			
}

// Las cajas grandes no pueden tener mas de 3 chocolates rellenos.
fact {all c:Caja | (c.tam in Grande) implies ((#(c.chocolates & formato.Relleno  )<4) ) }





// Utiliza las mismas palabras que el fact por eso es muy TRIVIAL, por ende ESTA MAL
check B1{all c:Caja | (c.chocolates in ChocoBlanco) or (c.chocolates in ChocoLeche) or (c.chocolates in ChocoSemiAmargo) or (c.chocolates.formato in Relleno) or (c.chocolates.formato in Tableta) }



///////////////////////////////////////////////////// VALIDO POSITIVAMENTE EL PRIMER FACT //////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////

// Para todas las cajas, si tiene UN SOLO FORMATO(formato esta en ONE) implica que pude tener cualquier tipo de chocolate
check MismoFormatoDistintoTipoChoco {all c: Caja | #(c.chocolates.formato)=1 implies #(c.chocolates & ChocoBlanco)>= 0 and #(c.chocolates & ChocoLeche)>= 0 and #(c.chocolates & ChocoSemiAmargo)>= 0  }

// Para todas las cajas, si los chocolates son TODOS del mismo TIPO implica que puede tener 1 O MAS FORMATO
check MismoTipoChocoDistintoFormatos {all c: Caja | ((c.chocolates in ChocoBlanco)or(c.chocolates in ChocoLeche)or(c.chocolates in ChocoSemiAmargo) ) implies #(c.chocolates.formato)>=1 }


// Los separo para hacer mas Bulto?? Puedo hacer lo mismo con el primero?????
check TodosChocoBlancoDistintosFormatos{all c: Caja | (c.chocolates in ChocoBlanco) implies  #(c.chocolates.formato)>=1  }
check TodosChocoLecheDistintosFormatos{all c: Caja | (c.chocolates in ChocoLeche) implies  #(c.chocolates.formato)>=1  }
check TodosChocoSemiAmargoDistintosFormatos{all c: Caja | (c.chocolates in ChocoSemiAmargo) implies  #(c.chocolates.formato)>=1  }


-------------------------OPCION CHEWER-------------------------
/* El siguiente run no genera instancias ya que le estoy pidiendo que en alguna caja haya chocolate de 
tipo ChocoBlanco y de tipo ChocoLeche, y que además tengan distinto formato, es decir, uno Tableta y otro Relleno.*/
run distintoTipoDistintoFormato { some c: Caja, ch1: ChocoBlanco, ch2: ChocoLeche | 
			ch1 in c.chocolates and 
			ch2 in c.chocolates and
			ch1.formato != ch2.formato	
} for 7



////////////////////////////////////////////////////////////// VALIDO POSITIVAMENTE EL SEGUNDO FACT //////////////////////////////////////////////////////////////////////////////////////

//ESTA ESA BIEN, no deberia de usar implies y chequear el extremo para que no retorne
run CajaGrandeMas3ChocoRelleno { some c:Caja | (c.tam in Grande)and(#(c.chocolates& formato.Relleno )>=4 ) }for 10

//   SIRVE ESTE??????????????????????????????????????
// No pongo caja Chica ya que no puede tener mas de 3 chocolates lo cual para pedir 4 relleno no me sirve
run CajaMedianaMas3ChocoRelleno { some c:Caja | (c.tam in Mediano)and(#(c.chocolates& formato.Relleno )>=4 ) } for 5

// O LO HAGO ASI???????????

/*El siguiente run genera instancias, ya que la caja es Mediana o chica */
run cajaMediana { some c: Caja, disj ch1, ch2, ch3, ch4: Chocolate | 
			(c.tam = Mediano) and
			ch1.formato = Relleno and
			ch2.formato = Relleno and
			ch3.formato = Relleno and
			ch4.formato = Relleno and
			ch1 in c.chocolates and
			ch2 in c.chocolates and
			ch3 in c.chocolates and
			ch4 in c.chocolates
} for 4




