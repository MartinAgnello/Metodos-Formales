abstract sig Chocolate { 
	formato: FormatoChoco 
}

sig ChocoBlanco, ChocoLeche, ChocoSemiAmargo extends Chocolate {} // tipo de chocolate

abstract sig FormatoChoco {}

one sig Tableta, Relleno extends FormatoChoco {}

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


---------------------------------------------------------------------------------------------------------------------------------------------

// Los chocolates dentro de una misma caja son del mismo tipo o poseen el mismo formato
fact { all c: Caja | mismoTipo[c] or mismoFormato[c] }

// predicado auxiliar que recibe una caja y verifica que solo haya chocolates de un mismo tipo
pred mismoTipo[c: Caja]{
	(c.chocolates in ChocoBlanco and 
	c.chocolates not in ChocoLeche and 
	c.chocolates not in ChocoSemiAmargo) or

	(c.chocolates not in ChocoBlanco and 
	c.chocolates in ChocoLeche and 
	c.chocolates not in ChocoSemiAmargo) or

	(c.chocolates not in ChocoBlanco and 
	c.chocolates not in ChocoLeche and 
	c.chocolates in ChocoSemiAmargo)
}

// predicado auxiliar que recibe una caja y verifica que solo haya chocolates de un mismo formato
pred mismoFormato[c: Caja]{
	c.chocolates.formato = Tableta or
	c.chocolates.formato = Relleno
}

/* El siguiente run no genera instancias ya que le estoy pidiendo que en alguna caja haya chocolate de 
tipo ChocoBlanco y de tipo ChocoLeche, y que además tengan distinto formato, es decir, uno Tableta y otro Relleno.*/
run distintoTipoDistintoFormato { some c: Caja, ch1: ChocoBlanco, ch2: ChocoLeche | 
			ch1 in c.chocolates and 
			ch2 in c.chocolates and
			ch1.formato != ch2.formato	
} for 7


/* El siguiente run genera instancias ya que le estoy pidiendo que en alguna caja
los chocolates tengan mismo formato. */
run distintoTipoMismoFormato  { some c: Caja, ch1: ChocoBlanco, ch2: ChocoLeche | 
			ch1 in c.chocolates and 
			ch2 in c.chocolates and
			ch1.formato = ch2.formato
}

/* El siguiente run genera instancias ya que le estoy pidiendo que en alguna caja
los chocolates tengan el mismo tipo, en éste caso ChocoBlanco. */
run mismoTipoDistintoFormato { some c: Caja, ch1, ch2: ChocoBlanco | 
			ch1 != ch2 and // me aseguro de que sean atomos diferentes
			ch1 in c.chocolates and 
			ch2 in c.chocolates and
			ch1.formato != ch2.formato
}

/* El siguiente run genera instancias ya que le estoy pidiendo que en alguna caja haya chocolates del
mismo tipo (ChocoBlanco en este caso), y que además tengan mismo formato. */
run mismoTipoMismoFormato { some c: Caja, ch1, ch2: ChocoBlanco | 
			ch1 != ch2 and // me aseguro de que sean atomos diferentes
			ch1 in c.chocolates and 
			ch2 in c.chocolates and
			ch1.formato = ch2.formato
}

---------------------------------------------------------------------------------------------------------------------------------------------

// Las cajas grandes no pueden tener más de 3 chocolates rellenos.
fact { no c: Caja | (c.tam = Grande) and #(c.chocolates & formato.Relleno) > 3 }

/*El siguiente run no genera instancias, ya que le estoy pidiendo que en una caja grande haya 4 chocolates 
distintos en formato Relleno */
run cajaGrandeMasDeTresRellenos { some c: Caja, disj ch1, ch2, ch3, ch4: Chocolate | 
			c.tam = Grande and
			ch1.formato = Relleno and
			ch2.formato = Relleno and
			ch3.formato = Relleno and
			ch4.formato = Relleno and
			ch1 in c.chocolates and
			ch2 in c.chocolates and
			ch3 in c.chocolates and
			ch4 in c.chocolates
} for 10

/* El siguiente run genera instancias ya que tengo 3 chocolates en formato relleno y caja tamaño grande */
run cajaGrandeTresRellenos { some c: Caja, disj ch1, ch2, ch3: Chocolate | 
			c.tam = Grande and
			ch1.formato = Relleno and
			ch2.formato = Relleno and
			ch3.formato = Relleno and
			ch1 in c.chocolates and
			ch2 in c.chocolates and
			ch3 in c.chocolates
} for 6

/*El siguiente run genera instancias, ya que la caja es Mediana o chica */
run cajaChica { some c: Caja, disj ch1, ch2, ch3, ch4: Chocolate | 
			(c.tam = Mediano or c.tam = Chico) and
			ch1.formato = Relleno and
			ch2.formato = Relleno and
			ch3.formato = Relleno and
			ch4.formato = Relleno and
			ch1 in c.chocolates and
			ch2 in c.chocolates and
			ch3 in c.chocolates and
			ch4 in c.chocolates
} for 4



---------------------------------------------------------------------------------------------------------------------------------------------

// INCISO B

/* Reemplazar un chocolate de una caja por otro chocolate. 

Esta acción es posible siempre y cuando:
	- la caja original posea al menos un chocolate relleno y
	- la caja original posea a lo sumo un chocolate blanco */
pred reemplazarChocolate[ch1, ch2: Chocolate, ca1, ca2: Caja]{
	(ch2 ! in ca1.chocolates) and
	(#(ca1.chocolates & formato.Relleno) >=1) and
	(ch2 in ca2.chocolates)
}

/* Caso de no exito: 
Se intenta reemplazar un chocolate, y que en la caja original no haya chocolates de formato Relleno.
En este caso funciona correctamente el predicado, ya que no genera instancias. */
run reemplazarChocolate_1_NE { some ch1, ch2: Chocolate, ca1, ca2: Caja |
	reemplazarChocolate[ch1, ch2, ca1, ca2] and
	(all ch3: Chocolate | ch3 in ca1.chocolates and ch3.formato != Relleno)
} for 7


/* Caso de no exito: 
Se intenta reemplazar un chocolate, y que en la caja original  haya 2 chocolates blancos.
En este caso NO funciona correctamente el predicado, ya que el run me encuentra instancias
en las que la caja original tiene 2 chocolates blancos, lo cual está mal. */
run reemplazarChocolate_2_NE { some ch1, ch2: Chocolate, ca1, ca2: Caja |
	reemplazarChocolate[ch1, ch2, ca1, ca2] and
	(some disj ch3, ch4: ChocoBlanco | ch3 in ca1.chocolates and ch4 in ca1.chocolates)
} for 7


/* Caso de no exito: 
Se intenta reemplazar un chocolate, y que en la caja original no exista el chocolate que se quiere reemplazar.
En este caso NO funciona correctamente el predicado, ya que el run me encuentra instancias
en las que la caja original no tiene el chocolate a reemplazar.*/
run reemplazarChocolate_3_NE { some ch1, ch2: Chocolate, ca1, ca2: Caja |
	reemplazarChocolate[ch1, ch2, ca1, ca2] and
	ch1 not in ca1.chocolates
} for 7


/* Caso de no exito: 
Se intenta reemplazar un chocolate, y que en la caja resultante no exista el chocolate nuevo.
En este caso funciona correctamente el predicado, ya que el run no encuentra instancias */
run reemplazarChocolate_4_NE { some ch1, ch2: Chocolate, ca1, ca2: Caja |
	reemplazarChocolate[ch1, ch2, ca1, ca2] and
	ch2 not in ca2.chocolates
} for 7


/* Caso de no exito: 
Se intenta reemplazar un chocolate, y que en la caja original ya exista el chocolate nuevo.
En este caso funciona correctamente el predicado, ya que el run no encuentra instancias */
run reemplazarChocolate_5_NE { some ch1, ch2: Chocolate, ca1, ca2: Caja |
	reemplazarChocolate[ch1, ch2, ca1, ca2] and
	ch2 in ca1.chocolates
} for 7


/* Caso de exito: 
Se intenta reemplazar un chocolate, y pidiendo que el chocolate original esté en la caja original
pero no esté en la caja final. Además que el chocolate final esté en la caja final y no en la original.
Que el chocolate a reemplazar sea distinto del reemplazado.
Que el resto de los chocolates (si hubiese) sean los mismos (esto sería parte del marco).
Tambien pido que la caja original posea al menos un chocolate relleno y a lo sumo un chocolate blanco
*/
run reemplazarChocolate_6_E { some disj ch1, ch2: Chocolate, ca1, ca2: Caja |
	reemplazarChocolate[ch1, ch2, ca1, ca2] and
	ch1 in ca1.chocolates and
	ch2 not in ca1.chocolates and
	ca2.chocolates = ca1.chocolates - ch1 + ch2 and

	// la caja original posea al menos un chocolate relleno
	(some ch3: Chocolate | ch3 in ca1.chocolates and ch3.formato = Relleno) and

	// la caja original posea a lo sumo un chocolate blanco
	(lone ch4: ChocoBlanco | ch4 in ca1.chocolates)

} 
