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

