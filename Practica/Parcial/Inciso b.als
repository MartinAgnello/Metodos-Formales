abstract sig Chocolate { formato: FormatoChoco }

sig ChocoBlanco, ChocoLeche, ChocoSemiAmargo extends Chocolate {}

abstract sig FormatoChoco {}

one sig Tableta, Relleno extends FormatoChoco {}

abstract sig Caja {
	tam: Tamanio,
	chocolates: some Chocolate
}
abstract sig Tamanio {}

one sig Chico, Mediano, Grande extends Tamanio {}

--------------------------------------------------------------------------------------------------------------------
//Factos

fact { all c: Caja | (c.tam = Chico) implies (#c.chocolates >=1 and #c.chocolates =<3) }
/*Para todas las cajas, si son chicas entonces tienen entre 1 y 3 chocolates*/

fact { all c: Caja | (c.tam = Mediano) implies (#c.chocolates >=4 and #c.chocolates =<5) }

fact { all c: Caja | (c.tam = Grande) implies (#c.chocolates >=6 and #c.chocolates =<7) }

fact { no disj c1, c2: Caja, c: Chocolate | (c in c1.chocolates) and (c in c2.chocolates) }
/*Lo leo al reves: c esta en la caja 1 y en la caja 2 si la caja 1 y 2 no son disjuntas o sea son la misma caja*/

/*INCISO A Los chocolates dentro de una misma caja son del mismo tipo o poseen el mismo formato.*/
fact {all caja: Caja | ( (caja.chocolates in ChocoBlanco) or (caja.chocolates in ChocoLeche) or (caja.chocolates in ChocoSemiAmargo) )
				or ( (caja.chocolates.formato in Tableta) or (caja.chocolates.formato in Relleno) )
 }

/*INCISO A Las cajas grandes no pueden tener mas de 3 chocolates rellenos.*/

fact {all caja: Caja | (caja.tam = Grande) implies ( #(caja.chocolates & formato.Relleno ) <= 3)}


----------------------------------------------------------------------------------------------------------------------------

/*INCISO B  
reemplazar un chocolate de una caja por otro chocolate. Esta accion es
posible siempre y cuando la caja original posea al menos un chocolate relleno y a lo sumo un chocolate blanco:
*/

pred reemplazarChocolate[ch1, ch2: Chocolate, ca1, ca2: Caja]{
	(ch2 ! in ca1.chocolates) and (#(ca1.chocolates & formato.Relleno) >=1) and (ch2 in ca2.chocolates) }

----------------------------------------------------------------------------------------------------------------------------
/*Proposito: Generar instancias donde la caja original posee mas de un chocolate blanco, cuando no se deberia poder
   Resultado: Se genero una instancia donde la caja1 (la original) posee 2 chocolates blancos
*/
run MasDeUnChocoBlanco {some caja1, caja2: Caja, ch1, ch2: Chocolate | reemplazarChocolate[ch1,ch2,caja1,caja2] and 
					#(caja1.chocolates & ChocoBlanco) >= 2 } 

/*Proposito: Generar instancias donde un chocolate que no pertenece a la caja original se reemplace por otro chocolate en la caja destino
   Resultado: Se genero una instancia donde se reemplaza un chocolate que no es de la caja original en la caja destino
*/
run ChNoEstaEnCaja1 {some caja1,caja2 : Caja, ch1, ch2: Chocolate | (ch1 !in caja1.chocolates) 
				and reemplazarChocolate[ch1,ch2,caja1,caja2]}

//  ch1 y ch2 pueden ser el mismo chocolate:
run Ch1Ch2MismoChocolate{some ch1, ch2: Chocolate, ca1, ca2: Caja | (ch1 = ch2 ) and reemplazarChocolate[ch1,ch2,ca1,ca2]} 

/*ch2 ya esta en la caja destino*/
run Ch2YaEsta {some caja1,caja2 : Caja, ch1, ch2: Chocolate | (ch2 in caja2.chocolates) and reemplazarChocolate[ch1,ch2,caja1,caja2] }

/*En ningun momento se reemplaza un chocolate por otro!
Proposito: Generar instancia 
*/
run Ch1SigueEnCaja1 { some ch1, ch2: Chocolate, ca1, ca2: Caja | (ch1 in caja2.chocolates) and ( ch2 in caja2.chocolates) 
				and reemplazarChocolate[ch1,ch2,caja1,caja2] }


