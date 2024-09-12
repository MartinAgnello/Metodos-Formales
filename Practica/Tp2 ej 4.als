sig Candidato { }

one sig Alejo, Luca, Carlos, David in Candidato { }
/*Define las signaturas que tienen 1 solo elemento, cada 1 de ellos incluidos en Candidato*/

one sig Maria {
	alto : set Candidato,
	moreno : set Candidato,
	buenmozo : set Candidato
}

/*Define una signatura Maria que tiene un único elemento 
alto : set Candidato: Define un atributo alto en la singatura Maria. 
Este atributo es un conjunto (set) de elementos de Candidato. 
Por lo tanto, alto es una relación que puede relacionar varios elementos de Candidato con Maria.
idem para moreno y buenmozo
*/
