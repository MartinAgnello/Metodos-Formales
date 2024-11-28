open util/ordering[Estado] as ord

abstract sig Objeto {}

/*En dinamica las signaturas en este caso extienden a Objeto*/
sig Misionero, Canibal extends Objeto {}

one sig Bote extends Objeto {}

/*La sig Estado existe si o si en estos problemas*/
sig Estado{
	orillaOeste: set Objeto,
	orillaEste: set Objeto	
}

fact {#Misionero = #Canibal}

/*Definimos el estado inicial del problema o sea que inicien todos en el lado Oeste de la orilla*/
fact {ord/first.orillaOeste = Objeto && no first.orillaEste}

/*b) Para que un estado sea valido, cada persona debe estar en alguna de las dos orillas del rıo.*/
pred esValido[e:Estado] {  
	( (#(e.orillaOeste & Canibal) <= #(e.orillaOeste & Misionero)) and 
	(#(e.orillaEste & Canibal) <= #(e.orillaEste & Misionero)) )
	or (
	( (#(e.orillaOeste & Canibal) > 0 and #(e.orillaOeste & Misionero) = 0) or 
	(#(e.orillaEste & Canibal) > 0 and #(e.orillaEste & Misionero) = 0) ) )
	and 
	/*el conj de objetos de la orilla oeste unido al conj de objetos de la orilla oeste es igual
	  a todos los objetos del problema. Con esto queremos decir que en c/estado no se pierdan objetos*/
	e.orillaOeste + e.orillaEste = Objeto
	and
	/*Que el mismo objeto no se encuentre en ambas orillas al mismo tiempo*/
	e.orillaOeste & e.orillaEste = none
}

fact {all e: Estado | esValido[e]}
--------------------------------------------------------------------------------------------------------------------------------------
/*c)Añadir hechos y/o predicados para la evolucion de los estados.
Agregaremos el cruce del rio*/

/*todos los estados menos el ultimo pueden modificarse en este orden*/

fact trace{all e: Estado - ord/last| let sigEst = e.next | 
		cruceOesteAEste[e,sigEst] or
		 cruceEsteAOeste[e,sigEst]
}


pred cruceOesteAEste[e_inicial, e_final: Estado]{
	Bote in e_inicial.orillaOeste and 
	/*creamos 2 personas que son objetos y excluimos al bote xq es un objeto tmbn
	hacemos para el caso en q cruzan 2 personas y en el q cruza 1*/
	((some disj p1, p2 : e_inicial.orillaOeste - Bote | 
							e_final.orillaEste = e_inicial.orillaEste +p1 +p2 + Bote 
							and
							e_final.orillaOeste = e_inicial.orillaOeste - p1 - p2 - Bote)
	or
	(some p1: e_inicial.orillaOeste - Bote | 
							e_final.orillaEste = e_inicial.orillaEste +p1 + Bote 
							and
							e_final.orillaOeste = e_inicial.orillaOeste - p1 - Bote))

}

pred cruceEsteAOeste[e_inicial, e_final: Estado]{
	Bote in e_inicial.orillaEste and 
	((some disj p1, p2 : e_inicial.orillaEste - Bote | 
							e_final.orillaOeste = e_inicial.orillaOeste +p1 +p2 + Bote 
							and
							e_final.orillaEste = e_inicial.orillaEste - p1 - p2 - Bote)
	or
	(some p1: e_inicial.orillaEste - Bote | 
							e_final.orillaOeste = e_inicial.orillaOeste +p1 + Bote 
							and
							e_final.orillaEste = e_inicial.orillaEste - p1 - Bote))
}

run {#Canibal = 3 and #Misionero = 3 and some e: Estado | e.orillaEste = Objeto} for 14

run copado{#Canibal = #Misionero and some e: Estado | e.orillaEste = Objeto} for 10

run copado2{#Canibal = 3 and some e: Estado | e.orillaEste = Objeto} for 10

/*Explicaciones:
Objeto: Es una entidad abstracta que actúa como una clase base. Todas las entidades que se encuentran en las 
orillas o en el bote extienden de esta signatura.
Estado: Representa una configuración del problema en un momento dado. 

ord/first.orillaOeste = Objeto && no first.orillaEste: Define el estado inicial del problema:
    -Todos los objetos (misioneros, caníbales y el bote) están en la orilla oeste.
    -No hay objetos en la orilla este al comienzo.

*/
