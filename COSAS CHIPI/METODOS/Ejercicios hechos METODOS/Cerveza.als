abstract sig Cerveza {
f: one Fermentacion

}

abstract sig Fermentacion { }
one sig Baja, Alta extends Fermentacion{ }

abstract sig Ale,Lager extends Cerveza{ }
sig Clara, Oscura in Cerveza{ }

sig Weisse,Ipa, Porter extends Ale{ }
sig Pilser, Bock extends Lager{ }

sig Pack {
contenido: some Cerveza 
}

fact{all p: Pack | (#(p.contenido)<7)}


// La cerveza Ale se fermentan a temperatura alta
fact { all c:Ale | c.f=Alta }

// La cerveza Lager se fermentan a temperatura baja
fact { all c:Lager | c.f=Baja }

//La cerveza Weisse es Clara
fact {all c:Weisse | c in Clara and c ! in Oscura }
// otra manera de escribir lo mismo 
// fact{all c:Cerveza | (c in Weisse)implies(c in Clara)  }

//La cerveza Pilser es clara
fact {all c:Pilser | (c in Clara) and (c ! in Oscura) }

//La cerveza Porter es Oscura 
fact {all c:Porter | (c ! in Clara) and (c in Oscura) }

//La cerveza Ipa y Bock son intermedias(claras y oscuras)
fact {all c:Ipa | (c in Clara) and (c in Oscura) }
fact {all c:Bock | (c in Clara) and (c in Oscura) }




// ejemplo para que me devuelva una cerveza Weisse y ver el resultado
run{some Bock}

