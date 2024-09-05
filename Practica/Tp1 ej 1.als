sig T {}

sig U {}

sig S {r: lone T}
/*Define el conj S, para cada atomo de S, este se vinculara con 0 o 1 atomos de T*/

sig S2 {r: one T}
/*Define el conj S2, para cada atomo de S2, este se vinculara con 1 atomo de T*/

sig S3 {r: T -> one U}
/*Define el conj S3, para las tuplas de los atomo de S3, cada atomo de T estara vinculado con un atomo de U, y a su vez cada atomo
de U estara vinculado con cualquier numero de atomos de T (por defecto T tiene "set" por delante)*/

sig S4 {r: T lone -> U}
/*Define el conj S4, para las tuplas con atomos de S4, para 0 o 1 atomos de T se vinculan con cualquier numero de atomos de U, 
a su vez cada atomo de U estara vinculado con 0 o 1 atomos de T*/

sig S5 {r: some T}
/*Define el conj S5, para cada atomo de S5, este se vinculara con 1 o mas atomos de T*/

sig S6 {r: set T}
/*Define el conj S6, para cada atomo de S6, este se vinculara con cualquier numero de atomos de T*/

sig S7 {r: T set -> set U}
/*Define el conj S7, para las tuplas de los atomos S7, a cualquier numero de T le corresponde cualquier numero de U*/

sig S8 {r: T one -> U}
/*Definde el conj S8, para las tuplas de los atomos S8, cada atomo de T se vincula con cualquier numero de atomos de U, a su vez
a cada U le corresponde exactamente un atomo de T*/
--------------------------

run SConMasDeUnT {one s:S, t:T | (s,t) | #t > 1}

run S2ConMasDeUnT{}

run S3TConMasDeUnU{}

run S4MasDeUnTConMismoU{}

run S5ConCeroT{}

run S6{}

run S7{}

run S8UConMasDeunT{}
