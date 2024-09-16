sig Guerrero {
	nom: one Nombre,
	ciu: one Ciudad,
	experto: one Arma,
	aporto: one Porcentaje
}

abstract sig Nombre{}
/*Si dejaramos nombre asi: sig Nombre{} entonces al no ser abstracta podria pasar q existan atomos 
de nombres que no sean ninguno de los nombres de los guerreros,lo cual para la definicion de nuestro modelo no tiene sentido,.
Ocurre lo mismo para Ciudad, Arma y Porcentaje*/

one sig Sargon, Urel, Hatussi extends Nombre {} 	
/*cada uno de ellos extiende a Guerreros para q sean disjuntos entre si, sino no tendria sentido*/

abstract sig Ciudad{}

one sig Elam, Akkad, Hatti extends Ciudad {}

abstract sig Arma {}

one sig Lanza, Espada, Hacha extends Arma{}

abstract sig Porcentaje {} 
/*Porcentaje no necesitamos manejarlo con numeros enteros, el enunciado nos dice q entre los 3 personajes aportan el 100%
uno aporta 40%, otro el 25%, y el ultimo lo calculamos nosotros que seria 35%. Conociendo los porcentajes podemos utilizarlos
para extender a Porcentaje*/

one sig Veinticinco, Treintaycinco, Cuarenta extends Porcentaje {}

---------------------------------------------

fact {#Guerrero = 3}	//Queremos q existan 3 guerreros

fact{no disj g1,g2: Guerrero | g1.nom = g2.nom} 

/*se lee no existen 2 atomos disjuntos de la signatura guerrero que los llamaremos g1 y g2, tales que comparten el mismo nombre.
Hacemos lo mismo para las ciudades*/

fact{no disj g1,g2: Guerrero | g1.ciu = g2.ciu } 

fact{all disj g1,g2: Guerrero | g1.experto != g2.experto } 
/*Se lee para todo par de guerreros que sean distintos su arma va a ser distinta*/

fact {all g1,g2: Guerrero | (g1 != g2) implies (g1.aporto != g2.aporto)}

/*
all g1,g2: Guerrero
Se lee para todo Guerrero, g1 y g2 que no necesariamente son distintos 
(g1 != g2) implies (g1.aporto != g2.aporto)
si son distintos, o sea, si g1 es distinto de g2, entonces que no hayan aportado lo mismo, o sea que el aporte sea distinto
La implicacion es implicacion logica, o sea, se hace verdadera en 3 casos y falsa en una.
*/

-------------------------------------------
//Modelando las restricciones del enunciado: 
/*Ur-El no es de Hatti, esto quiere decir: Existe un guerrero cuyo nombre es Ur-El que no viene de Hatti.*/

fact {one g : Guerrero | (g.nom = Urel) and (g.ciu != Hatti) } 

/*El guerrero que menos aportó es un experto con la lanza. Se podria hacer asi:
fact {one g : Guerrero | (g.aporto = Veinticinco) and (g.experto = Lanza)}
pero Noni le da un giro:
 */

fact {one g : Guerrero |  (g.experto = Lanza) and aportoElMenor[g]}

/*Sargón aportó un porcentaje mayor del ejército que el guerrero de Elam.*/
fact {one g1, g2 : Guerrero | (g1.nom = Sargon) and (g2.ciu = Elam) and aportoMayor[g1,g2] }

/*Hattusil, que no aportó el 40% del ejército, es un experto con el hacha. */
fact {one g : Guerrero | (g.nom = Hatussi)  and (g.experto = Hacha) and noAporto[g] }

/*El guerrero de Akkad es un experto con la espada.*/
fact { one g : Guerrero | (g.ciu = Akkad) and (g.experto = Espada) }

-------------------------------------------

pred aportoElMenor[g : Guerrero]{
/*Dentro del cuerpo del predicado escribimos la expresión booleana que determine que el Guerrero g es el que menos aporto*/
	(g.aporto = Veinticinco)
}

pred aportoMayor[g1,g2 : Guerrero]{
	(g1.aporto = Cuarenta) or	/*Si g1 aporto el 40 entonces es el que mas aporto*/
	( (g1.aporto = Treintaycinco) and (g2.aporto = Veinticinco) )
}

pred noAporto[g: Guerrero]{
	(g.aporto != Cuarenta)
}

-------------------------

run {} 

/*	Guerrero0: Sargon, Akkad, Espada, Cuarenta
 	Guerrero1: Hattusil, Hatti, Hacha, Treintaycinco
	Guerrero2: UrEl, Elam, Lanza, Veinticinco

*/




