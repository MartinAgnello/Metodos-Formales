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

/*VERSION MALA (creo) porque (caja.chocolates.formato in Relleno) le esta pidiendo el formato a todos los chocolates de la caja*/
// fact {all caja: Caja | (caja.tam = Grande) implies ( (caja.chocolates.formato in Relleno) and  (#(caja.chocolates) <= 3) )}

/*VERSION BUENA*/
fact {all caja: Caja | (caja.tam = Grande) implies ( #(caja.chocolates & formato.Relleno ) <= 3)}
----------------------------------------------------------------------------------------------------------------------------

/*Intentare generar una instancia en donde Los chocolates dentro de una misma caja no son del mismo tipo ni poseen el mismo formato.
Este run no genera instancias xq le estoy pidiendo para chocolates q esten dentro de una misma caja que sean de distinto formato y distinto tipo*/
run DistintoTipoYFormato { some caja: Caja, ch1,ch2: Chocolate | (ch1 in caja.chocolates) and (ch2 in caja.chocolates) and 
							(ch1.formato != ch2.formato) and (ch1 in ChocoBlanco) and (ch2 in ChocoSemiAmargo ) } for 6

/*El run Mas3Rellenos no genera instancias en donde la caja sea grande y la cantidad de chocolates de tipo relleno sean mayores q 3*/
run Mas3Rellenos {some caja: Caja | (caja.tam = Grande) and (#(caja.chocolates & formato.Relleno) > 3) } for 6




/*

*/
