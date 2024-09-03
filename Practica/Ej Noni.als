sig A {}

some sig B {}

abstract sig C {}

abstract sig D {}

one sig E {}

lone sig F {}

sig G extends C {}

sig H extends C {}

sig I in D {}

sig J extends G {}

sig K extends G {}

sig L extends B {}

sig M in G {}
----------------------

run { }

run { } for 5

run noHayB {no B}

run noHayE {#E = 0}

run masDeUnF {#F > 1}

run CnoGniH {some c:C | (c !in G) or (c !in H) } --OBS C es abstracta

run { some C - (G+H)}

run Dnol {some D-I }

run BnoL {some B-L}

//run GyHsimultaneo {some (G&H)}
run MyKsimultaneo {some (M&K)}

