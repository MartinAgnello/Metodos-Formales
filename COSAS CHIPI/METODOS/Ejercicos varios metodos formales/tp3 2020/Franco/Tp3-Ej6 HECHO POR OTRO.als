//--------------------------------------------------------------------------------------------------------------------------------------------------------------
//								Signaturas
//--------------------------------------------------------------------------------------------------------------------------------------------------------------
sig Bicicleta {
	rod: one Rodado,
	cam: set ModuloCambios
}
sig Playera, BMX, MountainBike extends Bicicleta {}

abstract sig ModuloCambios {}
sig Tres, Seis, Doce extends ModuloCambios {}

abstract sig Rodado {}
one sig Chico, Mediano, Grande extends Rodado {}

//--------------------------------------------------------------------------------------------------------------------------------------------------------------
//								Restricciones
//--------------------------------------------------------------------------------------------------------------------------------------------------------------
//No hay bicicletas que no sean Playeras, BMX o Mountain Bike
fact A { Bicicleta = (Playera+BMX+MountainBike) }
//Las bicicletas BMX no poseen cambios.
fact B { all b:BMX | #(b.cam)=0 }
//Las bicicletas mountain bike tienen cambios.
fact C { all b:MountainBike | #(b.cam)>0 }
//Las bicicletas playeras se encuentran disponibles en rodado chico o mediano.
fact D { Playera.rod=Chico or Playera.rod=Mediano }
//Las bicicletas BMX sólo se fabrican en rodado chico.
fact E { BMX.rod=Chico }
//El rodado de las bicicletas mountain bike es mediano o grande.
fact F { MountainBike.rod=Mediano or MountainBike.rod=Grande }
//Las bicicletas playeras chicas con cambios tienen 3 cambios.
//Las bicicletas playeras medianas con cambios tienen un total de 3 o 6 cambios.
fact G { 
	all p:Playera | some t:Tres |
	(p.cam=none) or
	(p.cam=t) or
	(p.rod=Mediano and seisCambios[p])
}
//Las bicicletas mountain bike medianas tienen un total de 3, 6 o 12 cambios.
//Las bicicletas mountain bike grandes tienen un total de 6 o 12 cambios.
fact H {
	all m:MountainBike | some t:Tres |
	(m.rod=Mediano and m.cam=t) or
	(seisCambios[m]) or
	(doceCambios[m])
}

//--------------------------------------------------------------------------------------------------------------------------------------------------------------
//								Predicados
//--------------------------------------------------------------------------------------------------------------------------------------------------------------
pred seisCambios[b:Bicicleta] {
	some c1,c2:ModuloCambios |
	((c1 in Tres and c2 in Tres) and b.cam=(c1+c2)) or
	((c1 in Seis) and b.cam=c1)
}
pred doceCambios[b:Bicicleta] {
	some c1,c2,c3,c4:ModuloCambios | 
	((c1 in Tres and c2 in Tres and c3 in Tres and c4 in Tres) and b.cam=(c1+c2+c3+c4)) or
	((c1 in Tres and c2 in Tres and c3 in Seis) and b.cam=(c1+c2+c3)) or
	((c1 in Seis and c2 in Seis) and b.cam=(c1+c2)) or
	((c1 in Doce) and b.cam=c1)
}
pred menorCantCambios[b:Bicicleta] {
	some t:Tres | 
	(b in Playera and b.cam=none) or
	(b in MountainBike and b.cam=t)
}
//Añadir un módulo de cambios a una bicicleta. 
//	+Solo bicicletas de rodado mediano.
//	+Deben poseer la menor cantidad de cambios posible.
pred anadirCambio[c:ModuloCambios,bi,bf:Bicicleta] {
	--Precondiciones
	(bi.rod=Mediano) and
	menorCantCambios[bi] and
	--Postcondiciones
	(bi!=bf) and
	(bf.cam = bi.cam+c) and
	(bf.rod=Mediano) and
	((bi in MountainBike and bf in MountainBike) or
	(bi in Playera and bf in Playera))
}

//--------------------------------------------------------------------------------------------------------------------------------------------------------------
//								Chequeos
//--------------------------------------------------------------------------------------------------------------------------------------------------------------
check A { no b:Bicicleta | b not in (Playera+BMX+MountainBike) }
check B { no c:ModuloCambios | some b:BMX | c in b.cam }
check C { no m:MountainBike | #(m.cam)=0 }
check D { no p:Playera | p.rod=Grande }
check E { no b:BMX | b.rod!=Chico }
check F { no m:MountainBike | m.rod=Chico }
check G { all p:Playera | 
		(#(p.cam)!=0) or
		(p.cam in Tres) or 
		(p.rod=Mediano and seisCambios[p])
}

check H { all m:MountainBike | 
		(m.rod=Mediano and m.cam in Tres) or
		(seisCambios[m]) or
		(doceCambios[m]) 
}

//--------------------------------------------------------------------------------------------------------------------------------------------------------------
//								Funciones
//--------------------------------------------------------------------------------------------------------------------------------------------------------------
fun med6Cambios[]:set Bicicleta {
	{b:Bicicleta | some t:Tres | b.rod=Mediano and ((b.cam=none) or (b.cam=t) or seisCambios[b])}
}

//--------------------------------------------------------------------------------------------------------------------------------------------------------------
//								Comandos
//--------------------------------------------------------------------------------------------------------------------------------------------------------------
run añadirExitoso1 { some bi,bf:Bicicleta, c:ModuloCambios | anadirCambio[c,bi,bf] } //Falla

run probarMed6Cambios1 { } for 10

























