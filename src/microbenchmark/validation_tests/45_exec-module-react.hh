"use hopscript"

module M1( in A ) 

   /*@ requires "True && emp" @*/
   /*@ ensures "True && ({A}.A?)  " @*/	

{

   emit A( 100 );
   async (A) {
      this.notify( 10 );
   };
}

module m( a, b ) 
   /*@ requires "True && emp" @*/
   /*@ ensures "True && ({A}.A?)  " @*/	

{
   run M1( a);
}

m.addEventListener( "a", e => console.log( "a=", e.nowval ) );
m.addEventListener( "b", e => console.log( "b=", e.nowval ) );

m.react();
m.react();
