sig T {}

sig U {}

sig S {r: lone T}
/*Define el conj S, para cada atomo de S, este se vinculara con 0 o 1 atomo de T*/

sig S2 {r: one T}

sig S3 {r: T -> one U}

sig S4 {r: T lone -> U}

sig S5 {r: some T}

sig S6 {r: set T}

sig S7 {r: T set -> set U}

sig S8 {r: T one -> U}

--------------------------

run SConMasDeUnT {one s:S, t:T | (s,t) | #t > 1}
