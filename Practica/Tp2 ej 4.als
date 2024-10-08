sig Candidato {
	nom : one Nombre,
	alt : one Altura,
	tez : one Tez,
	bn : one Viste
 }

abstract sig Nombre {}

one sig Alejo, Luca, Carlos, David extends Nombre { }

one sig Maria {
	alto : set Candidato,
	moreno : set Candidato,
	buenmozo : set Candidato
}

/*Define una signatura Maria que tiene un único atomo 
alto : set Candidato: Define la relacion alto, entonces Maria esta asociada con 0 o mas candidatos altos 
Por lo tanto, alto es una relación que puede relacionar varios elementos de Candidato con Maria.
idem para moreno y buenmozo
*/
abstract sig  Altura {}

one sig Alto extends Altura { }

one sig Bajo extends Altura {}

abstract  sig Tez { }

one sig Moreno, Blanco extends Tez { }

abstract  sig Viste {}

one sig BuenMozo extends Viste{ }

one sig Desastre extends Viste{ }


---------------------------------------------------------------------------


fact {#Candidato = 4}

/*Solo tres de los hombres son altos, solo dos son morenos, y solo uno es buenmozo.*/

fact {one c1,c2,c3 : Candidato | tresAltos[c1,c2,c3] and dosMorenos[c1,c2] and (c1.bn = BuenMozo) }


/*Cada uno de los cuatro hombres tiene al menos una de las caracterısticas buscadas por Marıa.*/

fact { one c1,c2,c3,c4:Candidato | (c1.alt = Alto) and (c2.tez = Moreno) and (c3.tez = Moreno) and (c4.alt = Alto)}



/*Alejo y Luca son morenos o no lo son*/

fact { one c1,c2 : Candidato | (c1.nom = Alejo and c2.nom = Luca) and ( ((c1.tez = Moreno) and (c2.tez = Moreno)) or 
													    	((c1.tez != Moreno ) and (c2.tez != Moreno)) ) }

/*Luca y Carlos tienen la misma altura.*/

fact {one c1,c2: Candidato | (c1.nom = Luca and c2.nom = Carlos) and (c1.alt = c2.alt)}

/*O bien Carlos es alto o David lo es, pero ambos no lo son.*/

fact {one c1,c2: Candidato | (c1.nom = Carlos and c2.nom = David) and ( ( (c1.alt = Alto) and (c2.alt != Alto) ) or 
														      ( (c1.alt != Alto) and (c2.alt = Alto) ) ) }
---------------------------

pred tresAltos(c1,c2,c3: Candidato){ 
	(c1.alt = Alto) and (c2.alt = c1.alt) and (c3.alt = c2.alt)
}


pred dosMorenos(c1,c2 : Candidato){
	(c1.tez = Moreno) and (c2.tez = Moreno)
}

-----------------------
run {  } for 4

/*
a) Analice el modelo brindado. Para ello, puede utilizar la funcionalidad de visualizacion provista por Alloy.
b) Genere instancias del modelo, sin restricciones adicionales, y analice sus caracterısticas.

El modelo genera un candidato que es el mismo para Alejo, Luca, Carlos y David
El modelo genera una Maria que esta asociada a ese candidato
*/

/*
c)Considere un escenario en el que Marıa tiene cuatro candidatos: Alejo, Luca, Carlos y David.
Dicha situacion ¿se corresponde con las instancias del modelo anteriormente generadas? En
caso negativo, añada las restricciones necesarias para modelar el escenario aquı planteado.

Rta: Modifique a Candidato para que sea una signatura abstracta e hice que Alejo, Luca, Carlos y David
extiendan a candidato asi son disjuntos.
*/

/*
d) agregar restricciones sobre el modelo para garantizar que:
+Solo tres de los hombres son altos, solo dos son morenos, y solo uno es buenmozo.
+Cada uno de los cuatro hombres tiene al menos una de las caracterısticas buscadas por Marıa.
+Alejo y Luca tienen la misma complexion (ambos son morenos o ambos no lo son).
+Luca y Carlos tienen la misma altura.
+O bien Carlos es alto o David lo es, pero ambos no lo son.

*/
