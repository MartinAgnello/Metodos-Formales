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
 
fact { all c: Caja | (c.tam = Chico) implies (#c.chocolates>=1 and #c.chocolates =<3) }
 
fact { all c: Caja | (c.tam = Mediano) implies (#c.chocolates >=4 and #c.chocolates =<5) }
 
fact { all c: Caja | (c.tam = Grande) implies (#c.chocolates >=6 and #c.chocolates =<7) }
 
// se tenia que comentar para poder hacer las cosas 
//fact { no disj c1, c2: Caja, c: Chocolate | (c in c1.chocolates) and (c in c2.chocolates) }

fact { all c:Caja | 
				// Mismo tipo
				( (c.chocolates in ChocoBlanco ) or (c.chocolates in ChocoLeche) or (c.chocolates in ChocoSemiAmargo) )or
				// Mismo FormatoChoco
				( (c.chocolates.formato in Tableta ) or (c.chocolates.formato in Relleno) )
			
}

fact {all c:Caja | (c.tam in Grande) implies ((#(c.chocolates & formato.Relleno  )<4) ) }


// Predicado dado en el enunciado 
// reemplazar un chocolate de una caja por otro chocolate. Esta accion es  posible siempre y cuando la caja original 
// posea al menos un chocolate relleno y a lo sumo un chocolate blanco
 pred reemplazarChocolateV2[ch1, ch2: Chocolate, ca1, ca2: Caja]{
  
  --Precondicion 
  (ch1 in ca1.chocolates) and
  (ch2 ! in ca1.chocolates) and
 // Puede haber 1 o mas chocolaes relleno	
  (#(ca1.chocolates & formato.Relleno) >=1) and
  //  Puede haber 0,1 chocolates blacos en la ca
  (#(ca1.chocolates & ChocoBlanco) < 2) and
  // ch1 tiene que ser distinto a ch2
  ch1!=ch2 and // ESTO NO ES NECESARIO por los dos in del principio

 --Marco
  ca1.chocolates-ch1 = ca2.chocolates-ch2 and

  --Postcondicion
  // chequeo que el chocolate ch2 este en la caja ca2
  (ch2 in ca2.chocolates) and
  // chequeo que el chocolate ch1 no este en la caja ca2	
  (ch1 !in ca2.chocolates) 

 }


// Caso de EXITO: estoy probando que la caja ca1 tenga 0 chocolates blanco, el predicado es verdadero por lo tanto retorna una instancia. Esta bien porque satisface al predicado
run CajaSinChocoBlanco {some ch1, ch2: Chocolate, ca1, ca2: Caja | #(ca1.chocolates & ChocoBlanco)=0 and reemplazarChocolateV2[ch1,ch2,ca1,ca2]  }for 7

// Caso de EXITO
run DiferentesTipos{ some ch1, ch2: Chocolate, ca1, ca2: Caja |  reemplazarChocolateV2[ch1,ch2,ca1,ca2] and (ch1 in ChocoBlanco) and (ch2 in ChocoLeche) } 

// Es un caso de NO EXITO, porque le estoy pidiendo que la caja 1 no tenga chocolates rellenos, lo cual hace que mi predicado sea falso y no retorne una instancia
run E2 {some ch1, ch2: Chocolate, ca1, ca2: Caja |  reemplazarChocolateV2[ch1,ch2,ca1,ca2] and (#(ca1.chocolates & formato.Relleno  )=0) }for 7

// Caso de NO EXITO
run DiferentesTamanos{ some ch1, ch2: Chocolate, ca1, ca2: Caja |  reemplazarChocolateV2[ch1,ch2,ca1,ca2] and (ca1.tam = Chico ) and (ca2.tam = Mediano) }


///////////////////////////////////////////////////////////////////////////////// CASOS DE CHEWER ////////////////////////////////////////////////////////////////////////////////

/* Caso de no exito:
	intento reemplazar un chocolate, y la caja cambia de tamaño.
	logicamente esto no debe generar instancias */
run reemplazarChocolateV2_1_NE { some disj ch1, ch2: Chocolate, ca1, ca2: Caja |
		reemplazarChocolateV2[ch1, ch2, ca1, ca2] and
		ca1.tam = Grande and 
		ca2.tam = Mediano
} for 7

/* Caso de no exito:
	intento reemplazar un chocolate en una caja sin chocolates.
	logicamente esto no debe generar instancias */
run reemplazarChocolateV2_2_NE { some disj ch1, ch2: Chocolate, ca1, ca2: Caja |
		reemplazarChocolateV2[ch1, ch2, ca1, ca2] and
		#ca1.chocolates = 0
} for 7

/* Caso de exito:
	intento reemplazar un chocolate blanco, por otro chocolate. */
run reemplazarChocolateV2_5_E { some disj ch1, ch2: Chocolate, ca1, ca2: Caja |
		reemplazarChocolateV2[ch1, ch2, ca1, ca2] and
		ch1 in ChocoBlanco
} 

/* Caso de exito:
	intento reemplazar un chocolate formato relleno, por otro chocolate. */
run reemplazarChocolateV2_6_E { some disj ch1, ch2: Chocolate, ca1, ca2: Caja |
		reemplazarChocolateV2[ch1, ch2, ca1, ca2] and
		ch1.formato = Relleno 
} for 5





///////////////////////////////////////////////////////////////////////////////////////// CONCLUSIONES /////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////


--Los casos de exito son cuando el predicado es verdadero, y no exito cuando el predicado es falso. Es cuando quiero que pase lo que puse. No importa si el predicado esta mal escrito, si da verdadero es de exito.
-- Cuando los run no son significativos: es cuando ya estan cubiertos por la definicion del predicado o estan cubiertos por un fact


// Este run es de NO EXITO porque estoy generando la descripcion donde mi predicado se hace falso porque le estoy pidinedo que el chocolate ch1 no este en la caja ca1, 
// al ser el predicado falso no me genero instancia
run B {some ch1, ch2: Chocolate, ca1, ca2: Caja | (ch1 !in ca1.chocolates) and reemplazarChocolateV2[ch1,ch2,ca1,ca2]}for 7		



----------------------------------------------------------- REDUNDANTES QUE HICE ---------------------------------------------------------------------------------------------------

// Los comandos A2, B2 y E no son significativos para validar la versión modificada del
// predicado ya que no contemplan casos distintos (todos quedan cubiertos por la definición del predicado).

run A2 {some ch1, ch2: Chocolate, ca1, ca2: Caja | (ch1 != ch2 ) and reemplazarChocolateV2[ch1,ch2,ca1,ca2]}
run B2 {some ch1, ch2: Chocolate, ca1, ca2: Caja | (ch1 in ca1.chocolates) and reemplazarChocolateV2[ch1,ch2,ca1,ca2]}
run E {some ch1, ch2: Chocolate, ca1, ca2: Caja |  reemplazarChocolateV2[ch1,ch2,ca1,ca2] and (#(ca1.chocolates & formato.Relleno  )> 0) }for 7

// NO SIRVE porque en predicado tengo puesto ch1!=ch2 por lo tanto estoy poniendo casi lo mismo por eso es REDUNDANTE
run A {some ch1, ch2: Chocolate, ca1, ca2: Caja | (ch1 = ch2 ) and reemplazarChocolateV2[ch1,ch2,ca1,ca2]}for 7

------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------


















