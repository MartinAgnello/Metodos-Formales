/*Cada libro puede pertenecer a una categoria, la cual esta conformada por todos los libros
que pertenecen a ella. Asimismo, cada libro puede clasificar a un conjunto de libros como
similares a el. Escriba un modelo en Alloy para representar este dominio, agregando las
restricciones que considere necesarias.
*/

sig Book{
	pertenece-> lone Category
	similiar -> set Book
} 

sig Category {
	tiene-> set Book 
}
