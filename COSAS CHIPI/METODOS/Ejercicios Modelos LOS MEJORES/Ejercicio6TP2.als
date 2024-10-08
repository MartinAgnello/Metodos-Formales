sig Casa {
			//Cada casa tiene tiene un color, si no ponen nada es ONE implicito 
			color: one ColorCasa,
			posicion: one PosicionCasa,
			duenio: one Persona
			//AGREGAR POSICION
}


abstract sig ColorCasa { }
// como solo hay una casa de cada color SI O SI tengo que poner ONE, ya que solo hay un atomo da cada uno
one sig Blanco, Amarillo, Verde, Rojo, Azul extends ColorCasa{ }

abstract sig PosicionCasa { }
// pasa lo mismo con posicion casa, solo hay una de cada una
one sig A,B,C,D,E extends PosicionCasa { }

sig Persona {
			// cada persona tiene un bebe, fuma, mascota y nacion, solo una por eso ONE
			bebe: one Bebida,
			fuma: one Cigarrillos,
			mascota: one Animal,
			nacion: one Nacionalidad
}

// aca pongo todas las opciones que hay, siempre hay ONE ya que solo cada uno esta relacionado a uno solo
// siempre pasa en los que hay que adivinar
abstract sig Bebida { }

one sig Te, Cafe, Leche, Cerveza, Agua extends Bebida { }

abstract sig Cigarrillos { }

one sig PallMall, Blends, Dunhill, BlueMaster, Prince extends Cigarrillos{ }

abstract sig Animal { }

one sig Perros, Gatos, Caballos, Pajaros, Peces extends Animal { }

abstract sig Nacionalidad { }

one sig Britanico, Sueco, Noruego, Danes, Aleman extends Nacionalidad { }

-----------------------------------------------------------------------------------------------
// FACTOOOOOOOUSSS

fact { all c:Casa |
    (c.pos=A and c.der.pos=B and #c.izq.pos=0) or
    (c.pos=B and c.der.pos=C and c.izq.pos=A) or
    (c.pos=C and c.der.pos=D and c.izq.pos=B) or
    (c.pos=D and c.der.pos=E and c.izq.pos=C) or
    (c.pos=E and #c.der.pos=0 and c.izq.pos=D)
}



run{ }

