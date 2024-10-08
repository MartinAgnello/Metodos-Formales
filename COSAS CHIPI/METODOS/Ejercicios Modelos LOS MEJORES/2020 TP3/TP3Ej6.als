// Bicicleta no es abstacta porque no tiene *
sig Bicicleta {
			// se usa ONE porque dice que es exactamente 1, el diagrama pone 1
			rod: one Rodado,
			// es un conjunto de Modulos, por eso uso SET, ya que puedo tener tres,seis y doce 
			// al mismo tiempo, tambien con set puedo representar el conjunto vacio, ya que
			// una bicileta puede no tener cambios
			cambios: set ModuloCambios

}
//una Bicileta puede ser de TIPO Playera, BMX, MountainBike
//Como bicleta solo puede ser o BMX O Playera o MontainBike y no dos o tres de estos al mismo tiempo
// se utiliza el EXTENDS
sig BMX, Playera, MountainBike extends Bicicleta { }

abstract sig Rodado{ }

//Solamente tiene un solo tipo de rodado ya que o es grande o es chico o es mediano
one sig Chico, Mediano, Grande extends Rodado { }

// Tiene * en el diagrama
abstract sig ModuloCambios { }

// aca uso extends ya que modulo solo puede ser de un tipo, pero una bicileta 
// puede tener mas de un modulo
sig Tres, Seis, Doce extends ModuloCambios { }


--------------------------------------------------------------------------

//Toda bicicleta es BMX, Playera o Mountain Bike
// al conjunto de bicicleta le saco los 3 tipos(BMX+ Playera+ MontainBike) me tendria que dar el conjunto vacio
// es para que no se cree bicileta sin tipo
fact A {no (Bicicleta - (BMX + Playera + MountainBike ))}

//Las bicicletas BMX no poseen cambios.
fact B { all b:BMX | #(b.cambios)=0 }

//Las bicicletas mountain bike tienen cambios.
fact C { all b:MountainBike | #(b.cambios)>0 }

//Las bicicletas playeras se encuentran disponibles en rodado chico o mediano.
// fact D { Playera.rod=Chico or Playera.rod=Mediano } ESTA MAL 
fact D { all p:Playera | (p.rod in Mediano) or(p.rod in Chico)  }


// Las bicicletas BMX solo se fabrican en rodado chico.
// aca tendria podria usar el = o in, En este caso da igual porque son singletonn 
fact E { all b:BMX | (b.rod in Chico ) }

// El rodado de las bicicletas mountain bike es mediano o grande
// fact F { MountainBike.rod=Mediano or MountainBike.rod=Grande } ESTA MAL
fact F { all m: MountainBike | (m.rod in Mediano) or (m.rod in Grande)  }

//Las bicicletas playeras chicas con cambios tienen 3 cambios.
//Las bicicletas playeras medianas con cambios tienen un total de 3 o 6 cambios.
// SI TIENE CAMBIOS, pero puede ser mediana o chica y NO TENER CAMBIOS
fact G{  
	// va asi con in o tendria que utilizar el =
	all p:Playera | // no tiene cambios
			      (p.cambios = none ) or
			      // si es de rodado chico solo puede tener un cambio de 3 
			      ( (p.rod in Chico) and ( tresCambios[p]) ) or 
			      // si es de rodado mediano un total de 3 o 6 cambios, 
			      ( (p.rod in Mediano ) and ( (seisCambios[p]) or ( tresCambios[p]) ) )
}


//Las bicicletas mountain bike medianas tienen un total de 3, 6 o 12 cambios.
//Las bicicletas mountain bike grandes tienen un total de 6 o 12 cambios.
fact H { 
	     all mb: MountainBike |
						(( mb.rod in Mediano ) and  (tresCambios[mb] or seisCambios[mb] or doceCambios[mb] ) )or
						( (mb.rod in Grande) and ( seisCambios[mb] or doceCambios[mb] ) ) 
}




---------------------------------------------------------------------------------------------
//                                             Predicados
---------------------------------------------------------------------------------------------
//PREGUNTA ACA HAGO PRICADO PARA REUTILIZACION?
//Tres cambios, donde es un unico modulo de 3 cambios 
pred tresCambios[b:Bicicleta]{
	//caso unico: un unico modulo de 3 cambios
	( ( one b.cambios ) and (b.cambios in Tres) )

}

// para tener 6 cambios una bici tiene que tener dos modulos de 3 o un modulo de 6
// para tener 6 cambios hay dos opciones: un modulo de 6 o dos modulos 3
pred seisCambios[b:Bicicleta]{	
 	//Caso 1: 1 solo modulo de 6 cambios
	(( one b.cambios ) and b.cambios in Seis) or
	//Caso 2: 2 modulos de 3 cambios
	( (#b.cambios = 2 ) and b.cambios in Tres )
} 

pred doceCambios[b: Bicicleta] {
	//Caso 1: Un solo modulo de 12 cambios	
	( (one b.cambios) and (b.cambios in Doce) ) or
	// Caso 2: Dos modulos de 6 cambios
	( (#b.cambios = 2 ) and (b.cambios in Seis) ) or
	// Caso 3: 1 Modulo de 6 cambios y 2 modulos de 3 cambios
	( (#b.cambios = 3 ) and (b.cambios in Seis + Tres ) ) or
	( (#b.cambios = 4) and (b.cambios in Tres))

}

// Pruebo que BMX no sea nulo el modulo de cambios
//run A{ some b:BMX | b.mod !in Tres }
run A { some b:BMX | b.cambios != none }for 5

// Pruebo que no exista una playera que tenga un modulo de 6 cambios y sea de rodado chico
run B {some p:Playera | (p.cambios in Seis) and #(p.cambios)=1 and (p.rod in Chico)}for 10

// otra opcion, vale???
run C {some p:Playera | (p.cambios in Seis) and seisCambios[p] and (p.rod in Chico)}for 10

// Pruebo que exista alguna Playera tal que tenga modulos de cambio de Seis y sea de Rodado Mediano
run D {some p:Playera | (p.cambios in Seis) and seisCambios[p] and (p.rod in Mediano)}

//Pruebo caso que sea rodado chico y 12 cambios, no debe devolver nada
run E {some mb:MountainBike | doceCambios[mb] and mb.rod in Chico  }

// VER QUE PASA
run F {some mb:MountainBike | (doceCambios[mb]) and (mb.rod in Grande) and (mb.cambios in Tres) }for 5

// pruebo que no puede existir una bmx con rodado grande o mediano
run G{some b:BMX | b.rod = Grande or b.rod = Mediano}

// pruebo que no puede existir una bmx con cambios
// esta bien el usar el >0 para cuando sabemos que no tiene??? 
run H{some b: BMX | #{b.cambios}>0  }

// Quiero probar que exista alguna mb con rodado grande, y un modulo solo de 3 cambios
run I {some mb:MountainBike | (mb.rod in Grande)and (#mb.cambios = 1)and (mb.cambios in Tres) }

// busca que lo que puse entre parentisis y busca un contraejemplo si no tira contraejemplo es que funciona lo que le pedi, Siempr  uso all
check casoBmx{all b:BMX  | #{b.cambios}=0 }






