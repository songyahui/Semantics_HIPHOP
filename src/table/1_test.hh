hiphop module prg(out Start, in A, in B, in C, in D, out O, out Done ) 
   /*@ requires "True && emp "@*/
 /*@ ensures  "True && ({})^*.{Done}" @*/
 /*@ ensures  "True && ({}.{}).{Done}" @*/
/*@ ensures  "True && ({}.{A}).{C}" @*/
/*@ ensures  "True && ({}.{A})^*.{C}" @*/
/*@ ensures  "True && ({}.{A})^*.{C}^*" @*/

/*@ ensures  "True && ({})^*.{A}" @*/
/*@ ensures  "True && ({}.{}).A?" @*/
/*@ ensures  "True && ({}.{C}).{Start}" @*/
/*@ ensures  "True && ({}.{Done})^*.{C}" @*/
/*@ ensures  "True && ({}.{})^*.{Start}^*" @*/
{
   emit Start();
   yield;
   async Done {
      emit A();
      if (B.now) {
         yield; 
         emit C()}
      else {
         yield; 
         emit D()};  
   };
   emit B (); 
   await Done;
}