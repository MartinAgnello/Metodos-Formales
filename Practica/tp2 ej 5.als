sig Objeto {}

sig Llave extends Objeto {r1: Mapeo some -> lone Valor }

sig Valor extends Objeto{r2: Mapeo some -> some Llave }

sig Mapeo {r3: Llave some  -> lone Valor}


//Otra forma:

sig Llave extends Objeto{
	llave_valor: lone Valor,
	llave_mapeo: set Mapeo

}

sig Valor extends Objeto{
	valor_llave: set Llave,
	valor_mapeo: set Mapeo
}

sig Mapeo{
	mapeo_valor: lone Valor,
	mapeo_llave: set Llave
}

-------------------------------------------

/*
b)¿Puede existir un objeto que no sea llave o valor? ¿Por que? Justifique especificando el
comando correspondiente en Alloy e indique la respuesta brindada por el analizador.*/

run { }

/*
c)Utilice una asercion para verificar si el mapeo define una relacion funcional parcial entre llaves
y valores. ¿Se verifica la asercion? En caso negativo, añada las restricciones necesarias sobre
el modelo para asegurar que se cumpla esta propiedad.
*/



/*
d)¿Puede existir una llave que no pertenezca a un determinado mapeo? ¿y un valor?. Intente
generar instancias en las que ocurran estas situaciones. ¿Fue posible generarlas? ¿Por que?
*/
