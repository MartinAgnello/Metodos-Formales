sig A {} //Definicion conjunto A

some sig B {}	//minimo que haya un atomo de B en el modelo

abstract sig C {}	//Todo atomo que pertenezca a C 
//sera de quien extienda a C, si es que es extendido.

abstract sig D {}

one sig E {}	//Toda instancia del modelo tendra un atomo de E

lone sig F {}	//Toda instancia del modelo tendra a lo sumo un atomo de F

sig G extends C {}

sig H extends C {}
/* G y H son disjuntas por definicion ya que extienden a C
*/

sig l in D {}	//las inclusiones no tienen la condicion de ser disjuntos si extienden
//a un mismo conjunto

sig J extends G {}

sig K extends G {}

sig L extends B {}

sig M in G {}
