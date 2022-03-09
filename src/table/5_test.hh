hiphop module prg(out Start, in A, in B, in C, in D, out O, out Done ) 
   /*@ requires "True && emp "@*/
// /*@ ensures  "True && ({})^*.{Done}" @*/
// /*@ ensures  "True && ({}.{}).{Done}" @*/
// /*@ ensures  "True && ({}.{A}).{C}" @*/
// /*@ ensures  "True && ({}.{A})^*.{C}" @*/
// /*@ ensures  "True && ({}.{A})^*.{C}^*" @*/

// /*@ ensures  "True && ({})^*.{A}" @*/
// /*@ ensures  "True && ({}.{}).A?" @*/
// /*@ ensures  "True && ({}.{C}).{Start}" @*/
// /*@ ensures  "True && ({}.{Done})^*.{C}" @*/
 /*@ ensures  "True && ({}.{})^*.{Start}^*" @*/
{
   try {
   try {
   emit Start();
   raise 1; 
   } catch {
      emit Done ();
   }}
   catch {
      emit C();
   }
   
}