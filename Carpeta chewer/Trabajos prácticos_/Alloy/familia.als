abstract sig Person {
	children: set Person,
	siblings: set Person
}

sig Man, Woman extends Person {}

sig Married in Person {
	spouse: one Married
}

////////////////////////////////////////////////////////////////////////
/////////////////////////////////Funciones///////////////////////////////
////////////////////////////////////////////////////////////////////////

//Funcion que permite identificar a los padres de una persona
fun parents [] : Person -> Person {
	~children
}

//Funcion que retorna el conjunto de personas sin padre ni madre
fun noPadreNoMadre[] : set Person {
	{p : Person | #p.parents = 0}
}

// Determinar si dos personas son parientes de sangre. (dos personas son parientes
// de sangre si poseen un ancestro en comun)
pred parientesDeSangre [p1,p2 : Person] {
	#(p1.^parents & p2.^parents) > 0
}
/////////////////////////////////////////////////////////////////////////
//////////////////////////////Hechos/////////////////////////////////////
/////////////////////////////////////////////////////////////////////////

fact {
	// Ninguna persona puede ser su propio padre/hijo
	//no p: Person | p in p.parents

	// Ninguna persona puede ser su propio ancestro
	no p : Person | p in p.^parents

	// Ninguna persona puede tener mas de una madre ni mas de un padre
	all p: Person | (lone (p.parents & Man)) and (lone (p.parents & Woman))

	//Los hermanos de una persona son aquellas personas que poseen un 	
	//padre en comun (es decir, considere la existencia de medio-hermanos).
	all p : Person | p.siblings = {q: Person |  some (p.parents & q.parents)} - p
     // el -p del final es para evitar que se incluya a la propia persona en la busqueda de hermanos

	//Dos parientes de sangre no pueden tener hijos en comun
	no p1,p2 : Person | (p1 != p2 and parientesDeSangre[p1,p2]) implies #(p1.children & p2.children)=0

	//Spouse debe ser simetrica
	spouse = ~ spouse

	//Ninguna persona puede estar casada consigo misma
	no m : Married | m.spouse = m  

	//Ninguna persona puede estar casada con mas de una persona
	no m : Married | #m.spouse > 1 

	//Ninguna persona puede estar casada con un familiar de sangre
	no m : Married | parientesDeSangre[m,m.spouse] 

	//Siblings es simetrica
	siblings = ~ siblings


	
}

////////////////////////////////////////////////////////////////////
////////////////////////////Aserciones///////////////////////////////
////////////////////////////////////////////////////////////////////

//Chequear si la relacion siblings es simetrica
assert hermanosDeHermanos {
	siblings = ~ siblings
} 

check hermanosDeHermanos 

//Chequear si es posible que dos parientes de sangre tengan hijos en comun
assert hijosEnComun {
	some p1,p2 : Person | parientesDeSangre[p1,p2] and some c : Person |
		c in p1.children and c in p2.children
}

check hijosEnComun //Encuentra contraejemplo, entonces es posible que dos parientes de
									// sangre tengan hijos en comun

//Chequear si la relacion spouse es simetrica
assert spouseSimetrica {
	all m : Married | m.spouse = m.spouse.spouse
}

check spouseSimetrica

//Chequear si es posible que una persona esta casada con mas de una persona
assert casadaConMasDeUna {
	all m : Married | lone (m.spouse)
}

check casadaConMasDeUna

//Chequear si es posible que una persona este casada consigo mismo
assert casadaConsigoMismo {
	all m : Married | m.spouse != m
}

check casadaConsigoMismo

//Chequear si es posible que una persona este casada con un familiar de sangre
assert casadaFamiliarSangre {
	all m : Married | !parientesDeSangre[m,m.spouse]
}

check casadaFamiliarSangre

//Chequear si es posible que hayan personas que no posean padre ni madre
assert niPadreNiMadre {
	all p : Person | #p.parents>0
} 

check niPadreNiMadre for 8


//Chequear si es posible que dos parientes de sangre tengan hijos en comun
assert parientesDeSangreHijos {
  some p1,p2 : Person | parientesDeSangre[p1,p2] and some c : Person | 
		c in p1.children and c in p2.children
}

check parientesDeSangreHijos

///////////////////////////////////////////////////////////////////////
/////////////////////// Ejecuciones//////////////////////////////////////
///////////////////////////////////////////////////////////////////////

run {} for 3

//Crear una instancia en la que las relaciones spouse y siblings no sean vacias.
run {#spouse>0 and #siblings>0} for 7

//Crear una instancia con dos parejas casadas diferentes.
run { some m1,m2 : Married | m1!=m2 and m1.spouse != m2} for 8

//Crear una instancia con a lo sumo un atomo en cada signatura de alto nivel y
//con un hombre casado

run {lone Person and some Man & Married} for 7


//Crear una instancia con a lo sumo dos atomos en cada signatura de alto nivel y
//con un hombre casado.

run {#Person < 3 and some Man & Married} for 8

//Crear una instancia donde haya a lo sumo una persona, alguna mujer y ningun
//hombre.

run {lone Person and some Woman and no Man} for 8


