
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


//DEBO COMENTARLO , ESTOY DICIENDO QUE HAY DOS CAJAS CON EN EL MOMENTO DE USAR ELIMINAR Y AGREGAR
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
  ch1!=ch2 and 

 --Marco
  ca1.chocolates-ch1 = ca2.chocolates-ch2 and

  --Postcondicion
  // chequeo que el chocolate ch2 este en la caja ca2
  (ch2 in ca2.chocolates) and
  // chequeo que el chocolate ch1 no este en la caja ca2	
  (ch1 !in ca2.chocolates) 

 }


// comportamiento de anadir un chocolate a una caja de tamano chico o mediano:
// Si la caja original ya posea la cantidad maxima de chocolates permitidos por su tamano, la operacion genera el 
// traspaso de su contenido a una caja del tamano inmediato siguiente, a la que se anade tambien el nuevo chocolate. 
// (Observacion: el tamano inmediato siguiente a chico es mediano, y el tamano inmediato siguiente a mediano es grande)

pred agregarChocolate[ch: Chocolate, ca1, ca2: Caja] {

 --Precondicion 
// No se define la precondición de que el chocolate no esté ya incluido en la caja "ca1". ???
// Esto es siempre que agrego algo
(ch !in ca1.chocolates)

 //Chequeo que ch este en los la caja ca2, 
 (ch in ca2.chocolates) and
 //chequeo que los chocolates de la caja ca1 este en la caja ca2
 (ca1.chocolates in ca2.chocolates)and
 //la caja ca1 tiene que ser de tamano chico o mediano
 ( (ca1.tam in Chico) or (ca1.tam in Mediano ) ) and 

 -- MARCO
// No se garantiza explícitamente la condición de marco de que se debe conservar el tamaño 
//cuando se intenta agregar un chocolate a una caja que no está llena. ESTA BIEN????? No tendria mucho setnido poner 
// el ultimo precondicion

// NOTA MARTIN: COMENTE LA SGTE LINEA XQ NO ME PARECIA Q TENGA SENTIDO PONERLE TAMAÑO A CA2 Y MAS 
// ADELANTE CAMBIARSELO, Y AHORA FUNCIONA
//( (ca1.tam in Chico and ca2.tam in Chico) or  (ca1.tam in Mediano and ca2.tam in Mediano) ) and
  

  --Postcondicion

    ca2.chocolates = ca1.chocolates + ch and
    ((#(ca1.chocolates)=3) implies  (ca2.tam = Mediano)) and 
    ((#(ca1.chocolates)=5) implies  (ca2.tam = Grande)) and
   //NOTA MARTIN: Agregado por mi al ver las correcciones
   //si no se sobre paso el tamaño de la caja entonces ca2 sera del mismo tamaño que ca1
    ((#(ca1.chocolates)<3) implies  (ca2.tam = Chico)) and
    ((#(ca1.chocolates)<5) implies  (ca2.tam = Mediano))
}

/*
caso DE EXITO: encontré una instancia en la cual se agrega un chocolate a una caja q ya tiene 3 chocolates.
se verifica q la caja pasa de chica a mediana. y que la caja final tiene al nuevo chocolate agregado
*/
run agregarChocolate_1_E { some ch: Chocolate, ca1, ca2: Caja |
						agregarChocolate[ch, ca1, ca2] and
							#ca1.chocolates = 3 and ca1.tam = Chico and ca2.tam = Mediano
} for 4
/*
caso de NO EXITO: no genera instancias ya que el tamaño de la caja es grande
*/
run agregarChocolate_5_NE { some ch: Chocolate, ca1, ca2: Caja |
						agregarChocolate[ch, ca1, ca2] and
						ca1.tam = Grande
} for 7















