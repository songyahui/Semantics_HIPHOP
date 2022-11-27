hiphop module prg(out Start, in A, in B, in C, in D, out O, out Done ) 
   /*@ requires "True && emp "@*/
/*@ ensures  "True && ({})^*.{Done}" @*/
/*@ ensures  "True && (({})^*.{Done})^*" @*/
/*@ ensures  "True && ({}.{A}).{C}.({})^*" @*/
/*@ ensures  "True && ({Start}.({})^*)^*" @*/
/*@ ensures  "True && ({})^*.{A}.({})^*" @*/
/*@ ensures  "True && ({})^*.{Done}.{}^*" @*/
/*@ ensures  "True && ({})^*.{Start}.{}^*" @*/
/*@ ensures  "True && ({})^*.{}.{}^*" @*/
/*@ ensures  "True && ({Start}.{A, B, Done}.({})^*)^*" @*/
/*@ ensures  "True && (({Start}.{A, B, Done}.({})^*)^*) \// ({})^*.{}.{}^*" @*/
/*@ ensures  "True && (({Start}.{A, B, Done}.({})^*)^*) \//  ({}.{}).B?" @*/


/*@ ensures  "True && ({}.{}).A?" @*/
/*@ ensures  "True && ({}.{}).B?" @*/
/*@ ensures  "True && ({}.{})^*.A?" @*/
/*@ ensures  "True && ({}^*.{C}.{D}.({}^*))^*" @*/
/*@ ensures  "True && ({}.{C}).{Start}" @*/
/*@ ensures  "True && ({}.{Done})^*.{C}.{Start}" @*/
/*@ ensures  "True && ({}.{Done})^*.{C}.({Done}^*).{Start}" @*/
/*@ ensures  "True && ({}.{})^*.{C}.{Start}" @*/
/*@ ensures  "True && ({}.{}.{})^*.{C}" @*/
/*@ ensures  "True && ({}.{})^*.{C}.{Start} \// ({}.{}.{})^*.{C}" @*/
/*@ ensures  "True && ({}.{}).A? \//  ({}.{}).B?" @*/
{
   present (Done()) {
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
   } else {
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
   };

    present (Done()) {
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
   } else {
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
   };
    
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
   present (Done()) {
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
   } else {
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
   };

   present (Done()) {
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
   } else {
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
   };

   present (Done()) {
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
   } else {
present (Done()) {
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
   } else {
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
   }
   };

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
      present (B()) {
         yield; 
         emit C()}
      else {
         yield; 
         emit D()};  
      present (C()) {
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

//30.889 237.2522 0.07164