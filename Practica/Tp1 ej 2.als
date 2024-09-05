/*adressBook = libreta de direcciones*/
abstract sig Target {}

abstract sig Name extends Target { addressBook: some Target }
/*Define el conj abstracto Name que extiende a Target, cada atodomo de Name esta vinculado a 1 o mas atomos de Target*/

sig Alias extends Name {}

sig Group extends Name {}

/*Alias y Group son disjuntos*/

sig Addr extends Target {}

/*Adrr y Name son disjuntos por lo tanto tmbn Adrr es disjunto con Alias y Group*/

/*Queremos llegar a esto:
--Target = {(Addr0), (Addr1), (Addr2), (Alias0), (Alias1), (Group0)}
--Name = {(Alias0), (Alias1), (Group0)}
--Alias = {(Alias0), (Alias1)}
--Group = {(Group0)}
--Addr = {(Addr0), (Addr1), (Addr2)}
--addressBook = {(Alias0,Addr0), (Alias0,Addr1), (Alias0,Addr2), (Alias0,Alias0),
(Alias0,Alias1), (Alias0,Group0), (Alias1,Addr0), (Alias1,Addr1), (Alias1,Addr2),
(Alias1,Alias0), (Alias1,Alias1), (Alias1,Group0), (Group0,Addr0), (Group0,Addr1),
(Group0,Addr2), (Group0,Alias0), (Group0,Alias1), (Group0,Group0)}
1 Alias con varios Adrr, varios Alias con varios Alias,
*/

--------------------------------------------------

run {} 
