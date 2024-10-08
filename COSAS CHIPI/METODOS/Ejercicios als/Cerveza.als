sig Cerveza {

temperatura: one Fermentacion,
tipo: one TipoCerveza,
color: one ColorCerveza,
cant: some Cantidad

}

abstract sig Fermentacion{ }
one sig Baja, Alta extends Fermentacion{ }

abstract sig TipoCerveza{ }
one sig Lager,Ale extends TipoCerveza{
tipo: one Cebada
 }

abstract sig Cebada{ }
one sig Pilser, Bock, Ipa,Weisse,Porter extends Cebada{ }


abstract sig Cantidad{ }
one sig Pack,Caja extends Cantidad{ }


abstract sig ColorCerveza{ }
one sig Clara,Oscura extends ColorCerveza{ }


fact {all c: Lager | (c.tipo = Bock) or (c.tipo = Pilser) }

fact{all c:Ale | (c.tipo = Weisse) or (c.tipo = Porter) or (c.tipo = Ipa) }








