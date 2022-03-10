hiphop module prg(out Start, in A, in B, in C, in D, out O, out Done ) 
   /*@ requires "True && emp "@*/
/*@ ensures  "True && ({}^*.{Done})^*" @*/
/*@ ensures  "True && ({}.{})^*.{Start}^*" @*/
/*@ ensures  "True && ({})^*.{Done}" @*/
/*@ ensures  "True && ({})^*.{A}.({}^*)" @*/
/*@ ensures  "True && ({}.{A}).{C}.({}^*)" @*/

/*@ ensures  "True && ({}.{A})^*.{C}.({})" @*/
/*@ ensures  "True && ({}.{C}).{Start}" @*/
/*@ ensures  "True && ({}.{}).A?" @*/
/*@ ensures  "True && ({}.{A})^*.{C}^*" @*/
/*@ ensures  "True && ({}.{}).{Done}.({}^*)" @*/

{
   yield;
   emit Start();
   yield;
      emit A();
     
         yield; 
         emit C();
    
         yield; 
         emit D();  
   emit B (); 
   emit Done ();

        yield;
   emit Start();
   yield;
      emit A();
     
         yield; 
         emit C();
    
         yield; 
         emit D();  
   emit B (); 
   emit Done ();

      yield;
   emit Start();
   yield;
      emit A();
     
         yield; 
         emit C();
    
         yield; 
         emit D();  
   emit B (); 
   emit Done ();

      yield;
   emit Start();
   yield;
      emit A();
     
         yield; 
         emit C();
    
         yield; 
         emit D();  
   emit B (); 
   emit Done ();

      yield;
   emit Start();
   yield;
      emit A();
     
         yield; 
         emit C();
    
         yield; 
         emit D();  
   emit B (); 
   emit Done ();

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