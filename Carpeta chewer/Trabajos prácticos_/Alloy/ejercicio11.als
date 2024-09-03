/*Considere el siguiente diagrama de clases, el cual modela la existencia de un almacenamiento
de mensajes, que gestiona el envio y recepcion de mensajes de computadoras que
tienen acceso autorizado a el. Un mensaje posee una computadora de origen, una computadora
destino, y un texto que representa el contenido del mensaje. Una computadora
puede enviar al almacenamiento un mensaje cuya destinataria sea una de sus computadoras
vecinas. Asimismo, una computadora puede recibir del almacenamiento un mensaje
del cual sea destinataria. El almacenamiento tiene limitaciones de espacio en cuanto a la
cantidad de mensajes que puede albergar (maximo 50 mensajes). De manera similar, el
almacenamiento no puede gestionar pedidos de mas de 5 computadoras autorizadas.*/

sig Mensaje{
	origen : one Computadora,
	destino : one Computadora,
	texto : one Texto
}

sig Almacenamiento{
	mensajes : set Mensaje,
	autorizadas : set Computadora
}

sig Computadora{
	vecinas : some Computadora	
}

sig Texto {}


////////////////////////////////////////////////////////////
//////////////////////FACTS////////////////////////////////
////////////////////////////////////////////////////////////

//El almacenamiento puede albergar 50 mensajes como maximo
fact capacidadAlmacenamiento {
	 #(Almacenamiento.mensajes) <= 50
}

//El almacenamiento no puede gestionar pedidos de mas de 5 computadoras autorizadas
fact capacidadComputadoras {
	#Almacenamiento.autorizadas <= 5
}


///////////////////////////////////////////////////////////
/////////////////////PREDICADOS//////////////////////////
//////////////////////////////////////////////////////////
pred enviarMensaje [envia,recibe: Computadora, viejo,nuevo: Almacenamiento, msj: Mensaje] {
		/*Condiciones para enviar un mensaje:
		-La computadora que envia el mensaje debe estar autorizada en el almacenamiento
		-Una computadora envia un mensaje para si misma o para una computadora vecina
		-El origen del mensaje debe ser la computadora que lo envia y el destino del mensaje
			la que lo recibe
			
			Si se cumplen las 3 condiciones:
		-El nuevo almacenamiento tendra los mismos mensajes que el almacenamiento viejo
			mas el mensaje que se envia
		-El nuevo almacenamiento tendra las mismas computadoras autorizadas que el 
			almacenamiento viejo

        */

		envia in viejo.autorizadas and (recibe=envia or recibe in envia.vecinas) and
		(msj.origen = envia and msj.destino = recibe) implies 
		nuevo.mensajes = viejo.mensajes + msj and nuevo.autorizadas= viejo.autorizadas
}

pred retirarMensaje [recibe: Computadora, viejo,nuevo: Almacenamiento, msj: Mensaje] {
	 /* Condiciones para retirar un mensaje:
     -El mensaje debe estar en el almacenamiento viejo
	-La computadora que recibe el mensaje debe estar entre las autorizadas en el almacenamiento
	-La computadora que retira el mensaje debe ser destinataria del mensaje
	
	Si ocurre esto:
	-El nuevo almacenamiento tendra los mismos mensajes que el almacenamiento viejo 
	menos el mensaje que se retira
	-El nuevo almacenamiento tendra las mismas computadoras autorizadas que el viejo

	*/
	msj in viejo.mensajes and recibe in viejo.autorizadas and recibe in msj.destino implies 
	nuevo.mensajes= viejo.mensajes-msj and nuevo.autorizadas= viejo.autorizadas

}

fun consultarMensaje [c:Computadora, a:Almacenamiento]: set Mensaje{
	//Conjunto de mensajes donde la computadora c es destinataria 
	// El mensaje debe estar en el almacenamiento
	// La computadora c debe estar entre las autorizadas
	{ m: Mensaje | m in a.mensajes and c in a.autorizadas and c in m.destino }
		
}

fun consultarMensajeVecinas [c:Computadora, a: Almacenamiento] : set Mensaje {
		//Conjunto de mensajes donde la computadora c es destinataria y el mensaje es de un vecino
		// El mensaje debe estar en el almacenamiento
		// La computadora c debe estar entre las autorizadas
		//El origen del mensaje debe ser de un vecino de la computadora

	{ m: Mensaje | m in a.mensajes and c in a.autorizadas and c in m.destino and m.origen in c.vecinas }
}


pred retirarMsjsVecinas [c:Computadora, viejo,nuevo: Almacenamiento] {
	c in viejo.autorizadas and nuevo.mensajes= viejo.mensajes - consultarMensajeVecinas[c,viejo]
	and nuevo.autorizadas = viejo.autorizadas
}

pred retirarMsjsDestinatario [c:Computadora, viejo,nuevo: Almacenamiento] {
	c in viejo.autorizadas and nuevo.mensajes= viejo.mensajes -consultarMensaje[c,viejo]
	and nuevo.autorizadas = viejo.autorizadas
}

pred agregarCompAut [nuevaComp : Computadora, viejo,nuevo: Almacenamiento] {
	nuevo.autorizadas = viejo.autorizadas+nuevaComp and
	nuevo.mensajes = viejo.mensajes
}

pred removerSiNoTieneMensj [comp : Computadora, viejo,nuevo: Almacenamiento] {
	/* Remover una computadora de las autorizadas unicamente si el almacenamiento no
			posee mensajes que la tengan como destinataria */
		comp in viejo.autorizadas and (no m : Mensaje | m in viejo.mensajes and comp in m.destino)
		  and nuevo.autorizadas = viejo.autorizadas - comp  and nuevo.mensajes = viejo.mensajes

}

pred removerYmantener [comp : Computadora, viejo,nuevo : Almacenamiento] {
		/*Remover una computadora del conjunto de computadoras autorizadas de un almacenamiento.
		Al remover dicha computadora, el almacenamiento mantiene todos los
			mensajes que la tengan como destinataria. */
		
		comp in viejo.autorizadas and nuevo.autorizadas= viejo.autorizadas - comp and
			nuevo.mensajes = viejo.mensajes 

}

pred removerYeliminar [comp: Computadora, viejo,nuevo : Almacenamiento] {
		/*Remover una computadora del conjunto de computadoras autorizadas de un almacenamiento.
			Al remover dicha computadora, el almacenamiento elimina todos los
		mensajes que la tengan como destinataria.*/

		comp in viejo.autorizadas and nuevo.autorizadas= viejo.autorizadas - comp and
			nuevo.mensajes = viejo.mensajes - consultarMensaje[comp,viejo]

}


///////////////////////////////////////////////////////////
/////////////////////EJECUCIONES/////////////////////////
/////////////////////////////////////////////////////////

//Test para enviarMensaje
run{some c,c1 :Computadora, v,n:Almacenamiento, men:Mensaje | enviarMensaje[c,c1,v,n,men] and
#(v.mensajes)=0 and #(n.mensajes)=1
} 
for  2

// Test para retirar mensaje
run{
	some c: Computadora, n, v:Almacenamiento, m:Mensaje | retirarMensaje[c,n,v,m] and #(v.mensajes)=1 and #(n.mensajes)=0
} for 2








