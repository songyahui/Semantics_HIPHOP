"use hiphop"
"use hopscript"

var hh = require( "hiphop" );

module prg( in A, in B, out O ) 
   /*@ requires "True && emp" @*/
   /*@ ensures "True && {}·A?·B?·{O}" @*/
      /*@ ensures "True && {}·A?·B?" @*/


{
   await( A );
   await( B );
   emit O;
}

exports.prg = new hh.ReactiveMachine( prg, "awaitseq" );
