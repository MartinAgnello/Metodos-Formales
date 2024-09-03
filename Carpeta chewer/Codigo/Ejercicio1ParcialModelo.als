sig A {} 
abstract sig B {}
sig C extends A {r : some B}
sig D extends A {s : set F}
sig E in B {}
sig F in B {}
sig G in A {t: D lone -> one E}

run{} for 3
