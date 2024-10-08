abstract sig Computadora{
	perifericos: set Periferico,
	inv_comp: one NumInv
}

sig Notebook, All_In_One, Desktop extends Computadora {}

abstract sig Periferico { inv_perif: one NumInv }

sig Mouse, Teclado, Monitor extends Periferico { }

sig NumInv { }

//fact { all disj c1, c2: Computadora | c1.inv_comp != c2.inv_comp }

fact { all disj p1, p2: Periferico | p1.inv_perif != p2.inv_perif }

fact { no c1, c2: Computadora, p: Periferico |
					(p in c1.perifericos) and
					(p in c2.perifericos) and
					(c1.inv_comp != c2.inv_comp)
}
------------------------------------------------------------------------------------------------------------------

// Las desktop tienen al menos un monitor. 
//fact { all c: Desktop | #(c.perifericos & Monitor) > 1 } 
 fact { all c: Desktop | (some m: Monitor | m in c.perifericos)} // ambas formas funcionan bien

// Caso general
run DesktopGeneral { #Desktop > 0 }

// Caso de no exito
run DesktopSinMonitor_1 { #Desktop > 0 and #Monitor = 0 } for 7
run DesktopSinMonitor_2 { one c: Desktop | #(c.perifericos & Monitor) = 0 } for 7

// Caso de exito: desktop con 2 monitores
run DesktopMonitores{ some c: Computadora | #(c.perifericos & Monitor) = 1 }

----------------------------------------------------------------------------------
// Las notebooks no tienen mouse ni teclado.

fact { all c: Notebook | #(c.perifericos & Mouse) = 0 and 
				#(c.perifericos & Teclado) = 0
}
/* // OTRA FORMA DE ESCRIBIRLO
fact { all c: Notebook | 
	(no m: Mouse | m in c.perifericos) and
	(no t: Teclado | t in c.perifericos)
}
*/

// Caso de exito: encuentra instancias pero ninguna tiene una Notebook vinculado a un Mouse
run NotebookSinMouse_1 { #Notebook > 0 and #Mouse > 0 } 

// Caso de no exito
run NotebookSinMouse_2 { some n: Notebook, m: Mouse | m in n.perifericos }
run NotebookSinTeclado_3 { some n: Notebook, t: Teclado| t in n.perifericos }


----------------------------------------------------------------------------------
// Las all-in-one y las desktop tienen al menos un teclado y al menos un mouse.

// hay 2 opciones
fact { all c: (All_In_One + Desktop) |
		#(c.perifericos & Teclado) >= 1 and
		#(c.perifericos & Mouse) >= 1
}

/*
fact { all c: (All_In_One + Desktop) |
	(some m: Mouse | m in c.perifericos) and
	(some t: Teclado | t in c.perifericos)
 }
*/

// Caso de no exito: AIO sin mouse
run AIODesktopConMouseYTeclado_1 { #All_In_One > 0 and #Mouse = 0 } for 7

// Caso de no exito: AIO sin teclado
run AIODesktopConMouseYTeclado_2 { #All_In_One > 0 and #Teclado = 0 } for 7

// Caso de no exito: Desktop sin mouse
run AIODesktopConMouseYTeclado_3 { #Desktop > 0 and #Mouse = 0 } for 7

// Caso de no exito: desktop sin teclado
run AIODesktopConMouseYTeclado_4 { #Desktop > 0 and #Teclado = 0 } for 7

// Caso de exito
run AIODesktopConMouseYTeclado_5 { some c: Computadora | 
			(c in All_In_One or c in Desktop) and
			Teclado in c.perifericos and
			Mouse in c.perifericos
}

----------------------------------------------------------------------------------

// Ninguna computadora puede tener más de 5 periféricos que sean monitores.
fact { no c: Computadora |  #(c.perifericos & Monitor) > 5 }
//fact { all c: Computadora | #(c.perifericos & Monitor) <= 5 }

// Caso de no exito: ya que hay mas de 5 monitores
run ComputadoraConCincoMonitores_1 { some c: Computadora | #(c.perifericos & Monitor) > 5 } for 10

// Caso de exito: hay al menos una computadora con 5 monitores
run ComputadoraConCincoMonitores_2 { some c: Computadora | #(c.perifericos & Monitor) = 5 } for 10

----------------------------------------------------------------------------------


// INCISO C

/*
añadir un periférico a una computadora desktop. 
Esta acción es posible siempre y cuando la computadora 
originalmente posea la misma cantidad de teclados y mouse
*/
pred agregarPeriferico[c1, c2: Computadora, p: Periferico] {
	not(#(c2.perifericos & Mouse) = #(c2.perifericos & Teclado)) and
	(p in c2.perifericos) and
	(c1.perifericos in c2.perifericos)
}
// DUDA: no se hace nada con el numero de inventario ? hay un fact que dice que no pueden ser iguales

-- Testear PRE:
// Caso de no exito: y sin embargo encuentra una instancia. 
// No deberia encontrar ya que c1 y c2 son de tipo AIO, cuando en realidad solo deberia funcionar para Desktop
run agregarPeriferico_1_NE { some c1, c2: All_In_One, p: Periferico | agregarPeriferico[c1,c2,p]  } for 10

// Caso de no exito: y sin embargo encuentra una instancia. 
// No deberia encontrar instancia ya que no se cumple la Precondicion de que
// la computadora c1 posea la misma cantidad de teclados y mouse
run agregarPeriferico_2_NE { some c1, c2: Desktop, p: Periferico | agregarPeriferico[c1,c2,p]  and
								(#(c1.perifericos & Teclado) != #(c1.perifericos & Mouse)) 
} for 7

-- Testear Marco:
// Caso de no exito: no deberia encontrar instancias, y sin embargo encuentra una
run agregarPeriferico_3_NE { some c1, c2: Desktop, p: Periferico | agregarPeriferico[c1,c2,p]  and
						not(c2.perifericos = c1.perifericos + p)
} for 4

// al pedo
run agregarPeriferico_4_NE { some c1, c2: Desktop, p1, p2: Periferico | agregarPeriferico[c1,c2,p1]  and
						c1.inv_comp = c2.inv_comp and
						p2 in c2.perifericos and
						p1 not in c1.perifericos
} for 4

// mismos perifericos

--Testear POS:



----------------------------------------------------------------------------------


// INCISO D

/*
Quitar un monitor de una all-in-one o de una notebook.

La cantidad de teclados y mouse de la computadora original 
no puede superar (en forma conjunta) su cantidad de monitores.

Luego del traspaso, la computadora deberá contar con al menos dos monitores.
*/
pred quitarMonitor[c1, c2: Computadora, p: Periferico]{
	-- pre
	// c1 y c2 tienen q ser AIO, o bien c1 y c2 tienen que ser notebook
	((c1 in All_In_One and c2 in All_In_One) or
	(c1 in Notebook and c2 in Notebook)) and // preguntar

	// p tiene que ser un monitor
	p in Monitor and

	// La cantidad de teclados y mouse de la computadora original no puede superar
	// (en forma conjunta) su cantidad de monitores.
	#(c1.perifericos & (Mouse + Teclado)) <= #(c1.perifericos & Monitor) and

	-- marco
	// c1 y c2 tienen el mismo numero de inventario
	c1.inv_comp = c2.inv_comp and

	-- post
	// la computadora no debe contar con al menos 2 monitores
	#(c2.perifericos & Monitor) >= 2 and 
	c2.perifericos = c1.perifericos - p

}

// caso general: DUDA!!!! preguntar por que a veces generamos 2 atomos y a veces 1
run quitarMonitor_1_E { some c1, c2: Computadora, p: Periferico | quitarMonitor[c1,c2,p] }

// caso de no exito
// La cantidad de teclados y mouse de la computadora original 
// supera su cantidad de monitores.
run quitarMonitor_2_NE { some c1, c2: Computadora, p: Periferico | quitarMonitor[c1, c2, p] and
					#(c1.perifericos & (Mouse + Teclado)) > #(c1.perifericos & Monitor)		
}

// caso de no exito: la computadora con menos de 2 monitores
run quitarMonitor_3_NE { some c1, c2: Computadora, p: Periferico | quitarMonitor[c1, c2, p] and
					#(c2.perifericos & Monitor) < 2 	
}

// caso de no exito: quitamos un mouse
run quitarMonitor_4_NE { some c1, c2: Computadora, p: Mouse | quitarMonitor[c1,c2,p] }

// caso de exito: a una notebook le quitamos su monitor
run quitarMonitor_5_E { some c1, c2: Notebook, p: Monitor| quitarMonitor[c1,c2,p] }

// caso de exito
run quitarMonitor_6_E { some c1, c2: All_In_One, p: Monitor| quitarMonitor[c1,c2,p] and
								c1.perifericos = c2.perifericos + p				
} for 5
// PODEMOS CREAR UN CASO DE NO EXITO POR TENER SCOPE MUY PEQUEÑO ???





----------------------------------------------------------------------------------


// INCISO E

/*
reemplazar un periférico por otro del mismo tipo en una all-in-one. 
Esta acción es posible siempre y cuando el periférico a reemplazar sea un teclado o un monitor
*/
pred reemplazarPeriferico[c1, c2: Computadora, p1, p2: Periferico]{
	(p1 in c1.perifericos) and
	(p2 !in c1.perifericos) and
	(p1 ! in Teclado + Monitor) and
	(c1.perifericos != c2.perifericos)
	(p2 in c2.perifericos)
}

// Caso de no exito: la computadora es una notebook
run reemplazarPerif_1 { some c1, c2: Notebook, p1, p2: Periferico | reemplazarPeriferico[c1,c2,p1,p2] }

// Caso de no exito: la computadora es una Desktop
run reemplazarPerif_2 { some c1, c2: Desktop, p1, p2: Periferico | reemplazarPeriferico[c1,c2,p1,p2] }

// Caso de no exito: el periferico es un mouse
run reemplazarPerif_3 { some c1, c2: Computadora, p1, p2: Mouse | reemplazarPeriferico[c1,c2,p1,p2] }

// Caso de exito: solamente funciona con mouse porque en el predicado dice "p1 ! in Teclado + Monitor"
run reemplazarPerif_4 { some c1, c2: Computadora, p1, p2: Teclado | reemplazarPeriferico[c1,c2,p1,p2] }

run reemplazarPerif_5 { some c1, c2: Computadora, p1, p2: Teclado | reemplazarPeriferico[c1,c2,p1,p2] 
								
}


pred reemplazarPeriferico[c1, c2: Computadora, p1, p2: Periferico]{
	-- pre
	p1 in c1.perifericos and 
	p2 not in c1.perifericos and
	c1 in All_In_One and
	c2 in All_In_One and
	((p1 in Monitor and p2 in Monitor) or
	(p1 in Teclado and p2 in Teclado)) and
	p1 != p2 and // deberiamos agregar que "p1.inv != p2.inv" ??
	
	-- marco
	c1.inv_comp = c2.inv_comp and
	c1.perifericos - p1 = c2.perifericos - p2 and
	
	-- post
	p2 in c2.perifericos and
	p1 not in c2.perifericos

}

