"use hiphop"
"use hopscript"

const hh = require( "hiphop" );

module prg( in A, in B, in R, out O ) 
   /*@ requires "True && emp" @*/
   /*@ ensures "True && {}·(A? // B?)·{O}" @*/
      /*@ ensures "True && {}·(A? . B?)·{O}" @*/

{


      fork {
	 await( A );
      } par {
	 await( B );
      };
      emit O;

}

exports.prg = new hh.ReactiveMachine( prg, "ABRO" );
