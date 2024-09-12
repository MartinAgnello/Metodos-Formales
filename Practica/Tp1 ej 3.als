one sig Juan, Pedro {}
/*Se definen dos signaturas, Juan y Pedro, usando la palabra clave one. Esto significa que cada una de estas signaturas contiene exactamente un 
único elemento (o instancia).*/

sig Culpable in univ {}
/*Se define la signatura Culpable, La declaración in univ indica que Culpable es un subconjunto del universo (univ), lo que significa que cualquier 
elemento puede estar en Culpable, incluido Juan, Pedro.*/

fact { Juan not in Culpable }
/*Hecho que establece que Juan no está en el conjunto de culpables.*/

fact { Juan in Culpable implies Pedro in Culpable }
/*Este hecho establece que si Juan estuviera en el conjunto de culpables, entonces Pedro también estaría en el conjunto de culpables.
Sin embargo, debido al Hecho 1, sabemos que Juan nunca estará en Culpable. Por lo tanto, este hecho nunca se activará */

assert conclusion { Pedro not in Culpable }
/*La aserción conclusion establece que Pedro no está en el conjunto de culpables.
Pero no hay ninguna restricción que impida que Pedro esté en Culpable, la aserción Pedro not in Culpable podría no ser válida.*/

----------------------
//run {} for 10

run {#Culpable > 5} for 10

check conclusion for 10

/*
Iniciso a
---INSTANCE---
integers={-8, -7, -6, -5, -4, -3, -2, -1, 0, 1, 2, 3, 4, 5, 6, 7}
univ={-1, -2, -3, -4, -5, -6, -7, -8, 0, 1, 2, 3, 4, 5, 6, 7, Juan$0, Pedro$0}
Int={-1, -2, -3, -4, -5, -6, -7, -8, 0, 1, 2, 3, 4, 5, 6, 7}
seq/Int={0, 1, 2, 3}
String={}
none={}
this/Juan={Juan$0}
this/Pedro={Pedro$0}
this/Culpable={}

Otra instancia:
integers={-8, -7, -6, -5, -4, -3, -2, -1, 0, 1, 2, 3, 4, 5, 6, 7}
univ={-1, -2, -3, -4, -5, -6, -7, -8, 0, 1, 2, 3, 4, 5, 6, 7, Juan$0, Pedro$0}
Int={-1, -2, -3, -4, -5, -6, -7, -8, 0, 1, 2, 3, 4, 5, 6, 7}
seq/Int={0, 1, 2, 3}
String={}
none={}
this/Juan={Juan$0}
this/Pedro={Pedro$0}
this/Culpable={-8, Pedro$0}
---------------------------------------

Inciso b decripto debajo de los hechos

---------------------------------------

Inciso c 
Observo que Juan y Pedro se encuentran en todas las instancias, que solo hay 1 Juan y 1 Pedro,
que Culpable puede ser vacio o tomar cualquier elemento del universo a excepcion de Juan.
---------------------------------------

Inciso d
¿Que observa con respecto al resultado mostrado por la herramienta? 
La herramienta dice: "Counterexample found.Assertion is invalid". 
El contra ejemplo que da:

---INSTANCE---
integers={-8, -7, -6, -5, -4, -3, -2, -1, 0, 1, 2, 3, 4, 5, 6, 7}
univ={-1, -2, -3, -4, -5, -6, -7, -8, 0, 1, 2, 3, 4, 5, 6, 7, Juan$0, Pedro$0}
Int={-1, -2, -3, -4, -5, -6, -7, -8, 0, 1, 2, 3, 4, 5, 6, 7}
seq/Int={0, 1, 2, 3, 4, 5, 6}
String={}
none={}
this/Juan={Juan$0}
this/Pedro={Pedro$0}
this/Culpable={Pedro$0}

Tiene sentido ya que Pedro no tiene ninguna restriccion para no estar en el conjunto Culpable, por lo tanto puede pertenecer a Culpable.

***********PREGUNTAR****************
¿Que sucede si se vuelve a chequear la asercion, habiendo removido el primer hecho? 
Me devuelve exactamente el mismo resultado, incluyendo la misma instancia.
Lo que cambia es que ahora si Juan se encuentra en Culpable, Pedro tambien.

*/
