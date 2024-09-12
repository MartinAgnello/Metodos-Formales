sig T {}

sig U {}

sig S {r: lone T}
/*Define el conj S, para cada atomo de S, este se vinculara con 0 o 1 atomos de T*/

sig S2 {r: one T}
/*Define el conj S2, para cada atomo de S2, este se vinculara con 1 atomo de T*/

sig S3 {r: T -> one U}
/*Define el conj S3, para las tuplas de los atomo de S3, cada atomo de T estara vinculado con un atomo de U, y a su vez cada atomo
de U estara vinculado con cualquier numero de atomos de T (por defecto T tiene "set"  0 o mas por delante)*/

sig S4 {ra: T lone -> U}
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

//run SConMasDeUnT {one s:S, t:T | (s,t) | #t > 1}
//run S {some s:S | #(s.r)=9} for 5 
/*Busca una instancia donde al menos un átomo s de S tenga exactamente 9 átomos de T asociados a través de la relación r.
Explicación de #(s.r)=9
s.r es la relación desde el átomo s hacia los átomos de T.
#(s.r) calcula la cantidad de átomos de T que están relacionados con el átomo s a través de la relación r.
Entonces, #(s.r)=9 significa que para el átomo s, la relación r debe conectar con exactamente 9 átomos distintos de T.
existe una instancia donde haya un atomo de S tq este relacionado con 9 t's.
*/

//run S2ConMasDeUnT{some s: S2 | #(s.2)=2}
/*Busca una instancia donde al menos un átomo s de S2 tenga exactamente 2 átomos distintos de T asociados a través de la relación r.*/

run S3TConMasDeUnU{some s:S3, u:U | #((s.r).u) = 3}  for 10

/* #((s.r).u) = 3 */

run prueba{some s:S4, u:U | #((s.ra).u) > 1 } for 10

run S5ConCeroT{}

run S6{}

run algo{#S4>0}
run S7{}


run S8UConMasDeunT{}
