"use hopscript"

var hh = require( "hiphop" );

function sum( arg1, arg2 ) {
   return arg1 + arg2;
};

module prg( out O ) 

   /*@ requires "True && emp" @*/
   /*@ ensures "True && {S, O}^* " @*/	


{

   loop {
      signal S ;//= 1;

      emit S( S.preval );
      emit O( S.nowval );

      yield;
   }
}

exports.prg = new hh.ReactiveMachine( prg, "emitvaluedlocal2" );
