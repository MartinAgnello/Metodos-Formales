/*
================ SIGNATURAS ================
*/
sig Bicicleta
{
	rod: one Rodado,
	cambios: set ModuloCambios
}

sig Playera, BMX, MountainBike extends Bicicleta {}

abstract sig Rodado {}

one sig Chico, Mediano, Grande extends Rodado {}

abstract sig ModuloCambios {}

sig Tres, Seis, Doce extends ModuloCambios {}


/*
================= HECHOS ===================
*/

//Las bicicletas BMX no poseen cambios.
fact {all b: BMX | no c: ModuloCambios | c in b.cambios}

//Las bicicletas playeras se encuentran disponibles en rodado chico o mediano. 
//fact {all b: Playera | one r: Rodado | b.rod = r and (r = Chico or r = Mediano)}

//Las bicicletas BMX sólo se fabrican en rodado chico.
fact {all b: BMX | one r: Rodado | b.rod = r and r = Chico}

//Las bicicletas playeras chicas con cambios tienen tres cambios. 
//Las bicicletas playeras medianas con cambios tienen un total de 3 o 6 cambios. 
fact {all b: Playera | some disj c1, c2: ModuloCambios | playeraChica[b, c1] or playeraMediana[b, c1, c2]}

//El rodado de las bicicletas Mountain Bike es Mediano o Grande
//Las bicicletas mountain bike medianas tienen un total de 3, 6 o 12 cambios. 
fact {all b: MountainBike | some disj c1, c2, c3, c4: ModuloCambios | mbMediana[b, c1, c2, c3, c4] or mbGrande[b, c1, c2, c3, c4]}

/*
================= PREDICADOS ===================
*/

//No existen bicicletas que no sean ni playera ni BMX ni mountain bike.
fact{no (Bicicleta - (BMX + Playera + MountainBike))}

//Todas las bicicletas playeras chicas. 
pred playeraChica[b: Playera, c1: ModuloCambios]
{
	c1 in Tres and
	(b.rod = Chico and (b.cambios = none or b.cambios = c1))
}

//Todas las bicicletas playeras medianas
pred playeraMediana[b: Bicicleta, c1, c2: ModuloCambios]
{
	b.rod = Mediano and 
	((b.cambios = none) or (c1 in Tres and b.cambios = c1) or seisCambios[b, c1, c2])
}

//Todas las bicicletas MountainBike medianas
pred mbMediana[b: Bicicleta, c1, c2, c3, c4: ModuloCambios]
{
	b.rod = Mediano and
	((c1 in Tres and b.cambios = c1) or (seisCambios[b, c1, c2]) or (doceCambios[b, c1, c2, c3, c4]))
}

//Todas las MountainBike grandes.
pred mbGrande[b: Bicicleta, c1, c2, c3, c4: ModuloCambios]
{
	b.rod = Grande and
	((seisCambios[b, c1, c2]) or (doceCambios[b, c1, c2, c3, c4]))
}

//Todas las posibles combinaciones para seis cambios.
pred seisCambios[b: Bicicleta, c1, c2: ModuloCambios]
{
	(c1 in Tres and c2 in Tres and b.cambios = (c1 + c2)) or
	(c1 in Seis and b.cambios = c1)
}

//Todas las posibles combinaciones para doce cambios. 
pred doceCambios[b: Bicicleta, c1, c2, c3, c4: ModuloCambios]
{
	((c1 in Tres) and (c2 in Tres) and (c3 in Tres) and (c4 in Tres) and (b.cambios = (c1 + c2 + c3 + c4))) or
	((c1 in Seis) and (c2 in Tres) and (c3 in Tres) and (b.cambios = (c1 + c2 + c3))) or
	((c1 in Seis) and (c2 in Seis) and (b.cambios = (c1 + c2))) or
	((c1 in Doce) and (b.cambios = c1))
}


run {} for 10
