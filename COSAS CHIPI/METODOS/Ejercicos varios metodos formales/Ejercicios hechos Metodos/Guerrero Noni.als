
sig Guerrero{
   nom: one Nombre,
   ciu: one Ciudad,
   experto: one Arma,
   aporto: one Porcentaje
}
// se usa el one sig para que no se creen dos con el mismo nombre por ejemplo Sargon1, Sargon2.
// run{#Sargon = 2} para ver que sin el one se crean dos Sargon
 abstract sig Nombre{ }
 one sig Sargon, UrEl, Hattusil extends Nombre{ }

 abstract sig Ciudad{ }
 one sig  Elam, Akkad, Hatti extends Ciudad{ }

 abstract sig Arma{ }
 one sig  Hacha, Espada, Lanza extends Arma{ }


 abstract sig Porcentaje{ }
 one sig Veinticinco, Treintaycinco, Cuarenta extends Porcentaje{ }

//Como solo hay 3 guerreros limito el numero a 3
 fact {#Guerrero = 3}

//No hay dos guerreros con el mismo nombre
 // No existe dos atomos disjuntos tal que compartan el mismo nombre
// no disj es no existe, y tal que es |
 fact { no disj g1,g2:Guerrero | g1.nom = g2.nom}

 fact { no disj g1,g2:Guerrero | g1.ciu = g2.ciu}

// No hay dos guerrerps que sean expertos con la misma arma
// es igual a las dos anteriores pero expresado de diferente manera
// Para TODO los atomos, tal que las armas son distintas(eso quiere decir lo que escribi)
// all disj estoy diciendo que g1 y g2 son distintos
 fact { all disj g1,g2:Guerrero | g1.experto != g2.experto}

 //No hay dos guerreros que haya aportado el mismo porcentaje al ejercito
// Para TODO guerreros g1,g2, si G1 es distinto G2, implica que g1 aporto un porcentaje distinta a g2.
// Esta afiermacion puede tener 3 interpretaciones cuando ambas sean verdaderas, 
// Aca no uso "all disj" uso "all" lo cual significa que g1 y g2 pueden ser iguales.
 fact {all g1,g2: Guerrero |  (g1 != g2) implies (g1.aporto != g2.aporto )}

//Ur-El no es Hatti
//decime que hay exactamente UN guerrero cuyo nombre es UrEl su ciudad no es Hatti
fact { one g: Guerrero | (g.nom = UrEl) and (g.ciu != Hatti) }

// El guerrero que aporto el menor porcentaje es experto con la lanza
// Creo el predicado aportoElMenor
// Escrito se leeria: existe un guerrero que aporto el menor porcentaje es el experto con la Lanza
fact {one g: Guerrero |  aportoElMenor[g] and (g.experto = Lanza)}


//Sargon aporto un porcentaje mayor que el guerrero de Elam
// Existe un guerrero g1 y un guerrero g2, tal que g1 su nombre es Sargon y g2 proviene de Elam y se verifica que el porcentaje
// del g1 es mayor que g2, el cual se hace el predicado aportoMayor
fact {one g1,g2:Guerrero | (g1.nom = Sargon) and (g2.ciu = Elam) and aportoMayor[g1,g2] }

//Hattsil no aporto el 40% y es experto con el haca
fact{one g:Guerrero | (g.nom = Hattusil) and (g.aporto != Cuarenta) and (g.experto = Hacha)}

//El guerrero de Akkad es experto con la espada
fact {one g: Guerrero | (g.ciu = Akkad) and (g.experto = Espada) }


--------------------------------------------------------------------

// como es el menor tiene que ser el Veinticinco
pred aportoElMenor[g:Guerrero] {
	(g.aporto = Veinticinco)

}

//Tengo 2 opciones, una que g1 hay aportado el 40% que seria el mayor
//La otra opcion es que g1 aporto el treintaycinco y g2 aporto el veiticinco  
pred aportoMayor[g1,g2: Guerrero]{
	(g1.aporto = Cuarenta) or
	((g1.aporto = Treintaycinco) and (g2.aporto = Veinticinco))

}

---------------------------------------------------------------------

run { }




















 
