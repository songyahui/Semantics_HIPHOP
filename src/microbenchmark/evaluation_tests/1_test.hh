module main(out Start, in A, in B, in C, in D, out O, out Done ) 
   /*@ requires "True && emp "@*/
 /*@ ensures  "True && ({})^*.{Done}" @*/
 /*@ ensures  "True && ({Start}·{A, B, BB}·{C}·{Done}) + {Start}·{A, BB, !B}·{D}·{Done}" @*/
/*@ ensures  "True && ({Start}·{A, B}·{C}·{Done}) + {}·{A, BB, !B}·{D}·{Done}" @*/
/*@ ensures  "True && ({}·{A, BB}·{C}·{}) + {}·{A, BB, !B}·{D}·{Done}" @*/
/*@ ensures  "True && ({}.{A})^*.{C}^*" @*/

/*@ ensures  "True && ({})^*.{A}" @*/
/*@ ensures  "True && ({}.{}).A?" @*/
/*@ ensures  "True && ({}.{C}).{Start}" @*/
/*@ ensures  "True && ({}.{Done})^*.{C}" @*/
/*@ ensures  "True && ({}.{})^*.{Start}^*" @*/
{
   emit Start();
   async Done {
      yield;
      emit A();
      present (B()) {
         yield; 
         emit C()}
      else {
         yield; 
         emit D()};  
   };
   yield;
   emit BB (); 
   await Done;
}