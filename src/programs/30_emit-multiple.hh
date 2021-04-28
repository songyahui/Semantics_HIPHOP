"use hopscropt"

const hh = require( "hiphop" );

hiphop module prg( A, B ) 

   /*@ requires "True && emp" @*/
   /*@ ensures "True && {A} . {B} " @*/	


{

   emit A();
   emit B();
}

const m = new hh.ReactiveMachine( prg );
m.debug_emitted_func = console.log;

m.react();
m.react();
