"use hopscropt"

const hh = require( "hiphop" );

module prg( out A, out B ) 

   /*@ requires "True && emp" @*/
   /*@ ensures "True && {A, B} " @*/	
   /*@ ensures "True && ({A, B})^* " @*/	


{

   emit A();
   emit B();
}

const m = new hh.ReactiveMachine( prg );
m.debug_emitted_func = console.log;

m.react();
m.react();
