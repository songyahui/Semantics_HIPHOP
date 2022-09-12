hiphop module prg(out Start, in A, in B, in C, in D, out O, out Done ) 
   /*@ requires "True && emp "@*/
/*@ ensures  "True && ({})^*.{Done}" @*/
/*@ ensures  "True && (({})^*.{Done})^*" @*/
/*@ ensures  "True && ({}.{A}).{C}.({})^*" @*/
/*@ ensures  "True && ({Start}.({})^*)^*" @*/
/*@ ensures  "True && ({})^*.{A}.({})^*" @*/
/*@ ensures  "True && ({})^*.{Done}.{}^*" @*/
/*@ ensures  "True && ({})^*.{Start}.{}^*" @*/
/*@ ensures  "True && ({})^*.{D,Done}.{}^*" @*/
/*@ ensures  "True && ({Start}.{A, B, Done}.({})^*)^*" @*/
/*@ ensures  "True && (({Start}.{A, B, Done}.({})^*)^*) \// ({})^*.{D,Done}.{}^*" @*/
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
   if (Done.now) {
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

   if (Done.now) {
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

   if (Done.now) {
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
if (Done.now) {
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

   try {
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
   emit Done ();};
   raise 0;
   }}
   catch {
      emit C();
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
      if (C.now) {
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