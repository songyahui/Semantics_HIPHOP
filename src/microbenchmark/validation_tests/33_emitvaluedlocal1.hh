"use hopscript"

var hh = require( "hiphop" );

hiphop module prg( out O ) 

   /*@ requires "True && emp" @*/
   /*@ ensures "True && ({S, O} + {O})^* " @*/	

{

   loop {
      signal S ;//= 1;
      
      emit S( S.preval  );
      emit O( S.nowval );
      yield;
      emit O( O.preval );
      yield;
   }
}

exports.prg = new hh.ReactiveMachine( prg, "emitvaluedlocal1" );
