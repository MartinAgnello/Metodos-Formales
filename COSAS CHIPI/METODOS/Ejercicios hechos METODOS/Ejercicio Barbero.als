
//Aca dice que cualquier Hombre afeita cualquier cantidad de personas (0,infinito)
sig Hombre { 

afeita: set Hombre
 }

// Aca estoy diciendo que una persona solo puede ser barbero una vez.??
one sig Barbero extends Hombre {}

// Todo hombre es afeitado por un Barbero 
// Un hombre x, y tal que y es distinto de x implica que x afeita a y
//  pred Afeita[x, y: Hombre] { (y != x) implies (x.afeita = y)}

//lo que tenia que hacer es poner !, entonces no crea una instancia ya que es una paradoja, no puede el barbero afeitarse ya que tambien es un hombre
fact { Barbero.afeita = {h: Hombre | h ! in h.afeita} }
