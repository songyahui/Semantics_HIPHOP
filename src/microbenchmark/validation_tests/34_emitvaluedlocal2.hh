"use hopscript"

var hh = require( "hiphop" );

function sum( arg1, arg2 ) {
   return arg1 + arg2;
};

module prg( out O ) 

   /*@ requires "True && emp" @*/
   /*@ ensures "True && {}·({S, O})^*" @*/	

   /*@ ensures "True && ({S, O})^*" @*/	

{

   loop {
      yield;
      signal S ;//= 1;

      emit S( );
      emit O(  );

      
   }
}

exports.prg = new hh.ReactiveMachine( prg, "emitvaluedlocal2" );
