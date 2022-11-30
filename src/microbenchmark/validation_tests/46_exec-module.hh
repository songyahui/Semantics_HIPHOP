"use hopscript"

module M1( in A , out B) 

   /*@ requires "True && emp" @*/
   /*@ ensures "True && {A, B}.{A}  " @*/	

{
   emit A( 100 );
   async A {
      emit B (); this.notify( 10 );
   };
}

module m( a, b ) 

   /*@ requires "True && emp" @*/
   /*@ ensures "True && {A, B}.{A}.{}  " @*/	


{
   run M1( a  );
   yield;
   // run M1( a ); // adding this line will couse failure on precondition check. 
}



m.addEventListener( "a", e => console.log( "a=", e.nowval ) );
m.addEventListener( "b", e => console.log( "b=", e.nowval ) );

m.react();
m.react();
m.react();
m.react();
m.react();
m.react();
m.react();
m.react();
