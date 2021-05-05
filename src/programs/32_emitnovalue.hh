"use hopscript"

var hh = require( "hiphop" );

hiphop module prg( out O ) 

   /*@ requires "True && emp" @*/
   /*@ ensures "True && {O}^* " @*/	

{

   loop {
      emit O( 5 );
      yield;
      emit O();
   }
}

exports.prg = new hh.ReactiveMachine( prg, "emitnovalue" );
