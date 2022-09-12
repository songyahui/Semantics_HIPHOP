hiphop module prg(out Start, in A, in B, in C, in D, out O, out Done ) 
   /*@ requires "True && emp "@*/
/*@ ensures  "True && ({}.{})^*.{Start}^*" @*/
/*@ ensures  "True && ({})^*.{Done}" @*/
/*@ ensures  "True && ({}.{}).{Done}.({}^*)" @*/
/*@ ensures  "True && ({})^*.{A}.({}^*)" @*/
 /*@ ensures  "True && ({}^*.{Done})^*" @*/

/*@ ensures  "True && ({}.{A})^*.{C}^*" @*/
/*@ ensures  "True && ({}.{}).A?" @*/
/*@ ensures  "True && ({}.{C}).{Start}" @*/
/*@ ensures  "True && ({}.{A}).{C}.({}^*)" @*/
/*@ ensures  "True && ({}.{A})^*.{C}.({}^*)" @*/

{
   yield;
   emit Start();
   yield;
      emit A();
      if (B.now) {
         yield; 
         emit C()}
      else {
         yield; 
         emit D()};  
   emit B (); 
   emit Done ();

      yield;
   emit Start();
   yield;
      emit A();
      if (B.now) {
         yield; 
         emit C()}
      else {
         yield; 
         emit D()};  
   emit B (); 
   emit Done ();

   emit A();

   {
      async Done {
        yield;
      };
      await Done; 
   };
   
   loop{
      emit Start();
   yield;
   {async Done {
      emit A();
      if (B.now) {
         yield; 
         emit C()}
      else {
         yield; 
         emit D()};  
   };
   emit B (); 
   emit Done ();}
   }
}

// 