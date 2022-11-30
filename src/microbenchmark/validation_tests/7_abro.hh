"use hiphop"
"use hopscript"

const hh = require( "hiphop" );

module prg( in A, in B, in R, out O ) 
   /*@ requires "True && emp" @*/
   /*@ ensures "True && (({A}//{B}).{O})^*" @*/
{

   do {
      fork {
	 await( A );
      } par {
	 await( B );
      };
      emit O;
   } every( R )
}

exports.prg = new hh.ReactiveMachine( prg, "ABRO" );
