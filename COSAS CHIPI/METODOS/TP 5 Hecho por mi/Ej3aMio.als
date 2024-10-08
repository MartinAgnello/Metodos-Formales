open util/ordering[Estado] as ord

sig Barco { }

sig Auto { }

abstract sig EstadoPuente { }

one sig Elevado, Bajo extends EstadoPuente { }

sig Estado {
	puente: one EstadoPuente,
	barcosEnEspera: some Barco,
	autosEnEspera: set Auto,
	autosEnPuente: one Auto
}

-------------------- Punto a-----------------------------

// "En toda instancia debe existir al menos dos barcos y dos autos"
// El modelo funciona mal ya que me encuentra un contraejemplo. 
check DosBarcosDosAutos { #Barco>= 2 and #Auto >=2 }

// "Por cuestiones de seguridad, en todo momento puede haber como maximo un auto sobre el puente."

// Para todo estado, que se satisfaga lo que me pide, en este caso que el puente no tenga mas de un auto
// al no devolver un contraejemplo, esta bien 
check MaxUnAutoCheck {all e:Estado | #e.autosEnPuente <= 1}
// Existe algun estado donde haya mas de un auto en el puente, al no existir ninguna instancia no devuelve nada
// por lo tanto 
run MaxUnAutoRun {some e:Estado | #e.autosEnPuente >1}

// Sin auto en el puente
// No encuentra instancias, lo cual esta mal, ya que deberia de poder no haber un auto en el puente
run NoAutoEnPuenteRun {some e: Estado | #e.autosEnPuente = 0}
// Como seria con check???
//check NoAutoEnPuenteCheck {all e:Estado | #e.autosEnPuente = 0 }

// Chequeo que pueda no haber barcos esperando
// no encuentra instancias, el modelo no permite que haya 0 barcos en la espera
run NoBarcosEnEspera {some e: Estado| #e.barcosEnEspera = 0}
