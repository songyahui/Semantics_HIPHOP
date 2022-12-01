"use hopscript"

var hh = require( "hiphop" );

module prg( out O ) 

   /*@ requires "True && emp" @*/
   /*@ ensures "True && {}·({O(5)}·{O})^* " @*/	

{

   loop {
            yield;
      emit O( 5 );
      yield;
      emit O();
   }
}

exports.prg = new hh.ReactiveMachine( prg, "emitnovalue" );
