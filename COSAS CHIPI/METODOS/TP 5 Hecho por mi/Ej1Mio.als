// Abro la utilidad de orden
// Voy a usar estados globales
open util/ordering[Estado] as est

/* definicion de las signaturas para los objetos */
 
abstract sig Objeto { }

// hay canibales y misioneros
sig Canibales,Misioneros extends Objeto { }

one sig Bote extends Objeto { }

sig Estado {
		orillaDerecha, orillaIzquierda: set Objeto
}

// Funciones para obtener canibales o misioners en la orilla en el estado que le paso
fun derCanibales[e: Estado]: set Canibales{
	e.orillaDerecha & Canibales
}

fun izqCanibales[e: Estado]: set Canibales{
	e.orillaIzquierda & Canibales
}

fun derMisioneros[e: Estado]: set Misioneros{
	e.orillaDerecha & Misioneros
}

fun izqMisioneros[e: Estado]: set Misioneros{
	e.orillaIzquierda & Misioneros
}

/* restricciones estaticas:  */
/* El nuumero de canibales que se encuentran cada orilla del rio en ningun momento puede superar al 
numero de misioneros en la misma orilla. Puede pasar que Misioneros sea 0.
 */
fact { all s: Estado |
	(#derCanibales[s] <= #derMisioneros[s] or #derMisioneros[s] = 0) and	
	(#izqCanibales[s] <= #izqMisioneros[s] or #izqMisioneros[s] = 0)
}

// Defino estado inicial: todos estan en la orilla derecha
fact estadoInicial { est/first.orillaDerecha = Objeto and est/first.orillaIzquierda= none }

---------------- PUNTO B ------------------

// Para que un estado sea valido, cada persona debe estar en alguna de las dos orillas del rIo.

pred esValido[e:Estado] {

	#((e.orillaDerecha+e.orillaIzquierda) & Canibales) = #((e.orillaDerecha + e.orillaIzquierda) & Misioneros)
	and (Bote in e.orillaDerecha or Bote in e.orillaIzquierda)

}

/* asegurar que todos los estados son validos */
fact{ all e:Estado | esValido[e]  }

/* definir operaciones de cambio*/

pred CruzarElRio[e1,e2:Estado]{
	// El bote esta en la orilla derecha
	((Bote in e1.orillaDerecha) implies (
	-- cruza una persona de derecha a izquierda
	(some persona1: e1.orillaDerecha |  -- alguna persona que este en el estado1 orilla derecha
		-- persona1 no es el bote
		persona1 != Bote and
		-- chequeo que se mantengan las cantidad de personas bien de estado1 a estado2
		e2.orillaDerecha = e1.orillaDerecha - Bote - persona1 and
		e2.orillaIzquierda = e1.orillaIzquierda + Bote + persona1
	)
	or
	--cruzan 2 personas de derecha a izquierda
	(some disj persona2, persona3 : e1.orillaDerecha |
	-- persona 2 y 3 no son un bote
	persona2 != Bote and persona3 != Bote and
	-- chequeo
	e2.orillaDerecha = e1.orillaDerecha - Bote - persona2 - persona3 and
	e2.orillaIzquierda = e1.orillaIzquierda + Bote + persona2 + persona3)
	
	))and
	-- El bote esta en la orilla izquierda
	((Bote in e1.orillaIzquierda) implies (
	--cruza una persona de izquierda a derecha
	(some persona4: e1.orillaIzquierda |
		-- persona4 no es el bote 
		persona4 != Bote and
		-- chequeo que se mantengan las cantidad de personas bien de estado1 a estado2
		e2.orillaIzquierda = e1.orillaIzquierda - Bote - persona4 and
		e2.orillaDerecha = e1.orillaDerecha + Bote + persona4)
	or
	-- cruzan 2 personas de izquierda a derecha
	(some disj persona5, persona6: e1.orillaIzquierda |
	-- persona5 y 5 no son bote
	persona5 != Bote and persona6 != Bote and
	--chequeo 
	e2.orillaIzquierda = e1.orillaIzquierda - Bote - persona5 - persona6 and
	e2.orillaDerecha = e1.orillaDerecha + Bote + persona5 + persona6)
	)-- cierre del imples orillaIzquierda
	)-- cierre del Bote in e1.orillaIzquierda

}


/* cambios de estados*/

fact traces {
	all e:Estado-est/last | let es = e.next | CruzarElRio[e,es]	
}


run {  } for 10 but 10 Estado

run canibales3misioneros3 { #Canibales = 3 and #Misioneros = 3 } for 9

run { #Canibales = 3  and some e:Estado | e.orillaIzquierda=Objeto} for 12






