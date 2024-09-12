sig Casa {
	color : one ColorCasa,	// cada casa tiene un color
	posicion: one PosicionCasa,
	duenio: one Persona

}

abstract sig ColorCasa {}

one sig Blanco, Amarillo, Verde, Rojo, Azul extends ColorCasa {}  //como no hay mas de una casa blanca/azul/.. entonces solo hay 1 de c/1

abstract sig PosicionCasa {}

one sig A, B, C, D, E extends PosicionCasa {}	//como no hay mas de una posicion A/B/.. entonces solo hay 1 de c/1

sig Persona {

	bebe: one Bebida,
	fuma: one Cigarrillos,
	mascota: one Animal,
	nacion: one Nacionalidad
}

abstract sig Bebida{}

one sig Te, Cafe, Leche, Cerveza, Agua extends Bebida{}

abstract sig Cigarrillos{}

one sig PallMall, Blends, Dunhill, BlueMaster, Prince extends Cigarrillos {}

abstract sig Animal{}

one sig Perros, Gatos, Caballos, Pajaros, Peces extends Animal {}

abstract sig Nacionalidad{}

one sig Britanico, Sueco, Noruego, Danes, Aleman extends Nacionalidad {}

---------------------------------------

run {} 
/*Si solo corremos el run vamos a tener 2 casas y 3 personas y esto no es lo q buscamos entonces tenemos que empezar a 
agregar restricciones 
falta modelar la relacion de cercania entre casas
*/
