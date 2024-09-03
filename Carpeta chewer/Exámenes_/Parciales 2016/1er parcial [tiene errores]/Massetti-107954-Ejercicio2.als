sig Departamento {
		dictadoHabilitado : Materia -> some Departamento
}

sig Materia {
	pertenece : one Departamento
}

sig Carrera {
	dptoCabecera : one Departamento,
	materias : some Materia
}


/*Las materias de una carrera deben ser tales que su dictado se encuentre habilitado
	por el departamento de cabecera de la carrera */

fact dictadoHabilitado {
	all c : Carrera , dpto, dptoCab : Departamento, m : Materia| 
			dptoCab = c.dptoCabecera and m in c.materias
				 and (m->dpto) in dptoCab.dictadoHabilitado

}


//Determinar si es posible agregar una materia a una carrera
pred agregarMateria [m : Materia, c : Carrera] {
	some dpto,dptoCab : Departamento | dptoCab = c.dptoCabecera and 
		(m->dpto) in dptoCab.dictadoHabilitado
		
}

//Determinar si es posible quitar una materia de una carrera
pred quitarMateria [m:Materia, c : Carrera] {
	m in c.materias
}

/* Dados dos conjuntos de materias (CM1 y CM2), determinar si es posible realizar un
cambio de plan flexible de una carrera. El cambio flexible implica realizar los cambios
posibles correspondientes al anadido de materias de CM1 y la remocion de materias de CM2*/

pred cambioFlexible [cm1: set Materia, cm2: set Materia] {
	some c : Carrera,  mat1,mat2 : Materia| cm1 in c.materias and cm2 in c.materias and
		mat1 in cm1 and mat2 in cm2 and agregarMateria[mat1,c] and quitarMateria[mat2,c]

}









run {} for 3
