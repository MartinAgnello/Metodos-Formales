sig Conjunto { elementos: set Elemento }	/*le pongo set para que el conj vacio este considerado*/

sig Elemento { }

-------------------------------
/*fact { all c1: Conjunto | some c2: Conjunto, e: Elemento |
(c1.elementos = c2.elementos + e) and (e ! in c1.elementos) }*/

/*
Facto: 
Para todos los conjuntos c1
existe al menos un conjunto c2 y un elemento e, tq satisfacen:
el conjunto c1 es igual al conjunto c2 unido al elemento e
y
el elemento e no esta incluido en los elementos de c1

Interpretación general:

Este hecho afirma que para cualquier conjunto c1, existe algún conjunto c2 y algún elemento e tales que:
	El conjunto c1 es igual al conjunto c2 más el elemento e.
	El elemento e no estaba previamente en los elementos de c1 antes de ser añadido.
*/

------------------------------
pred pertenece( e: Elemento, c: Conjunto){
	e in c.elementos
}

pred conjunto_vacio(c1 : Conjunto){
	#(c1.elementos) = 0
}

------------------------------

fact{ all c1,c2: Conjunto | (c1.elementos = c2.elementos) implies (c1 = c2) }
/*Si dos conjuntos poseen los mismos elementos, entonces son el mismo conjunto.*/

fact {all e: Elemento, c:Conjunto | (e in c.elementos) implies pertenece[e,c]}
/*Se dice que un elemento (o miembro) pertenece a un conjunto si esta incluido de algun
modo dentro de el.*/

fact{ all c1:Conjunto | #(c1.elementos) = 0 implies conjunto_vacio[c1]}

------------------------------
//Inciso c: todo conjunto puede expresarse como la union de dos conjuntos

assert conj_cerrado{all disj c1,c2,c3: Conjunto | c1.elementos = (c2.elementos + c3.elementos)}
------------------------------

//run { some c1,c2 : Conjunto |  (c1.elementos = c2.elementos) } 

check conj_cerrado

/*
Se dice que un elemento (o miembro) pertenece a un conjunto si esta incluido de algun
modo dentro de el. Si dos conjuntos poseen los mismos elementos, entonces son el mismo conjunto.
El conjunto que no contiene elementos se llama conjunto vacıo, denotado como ∅ o {}, y claramente
es un conjunto.
*/
