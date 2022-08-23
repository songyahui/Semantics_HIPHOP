"use hiphop"
"use hopscript"

var hh = require("hiphop");

hiphop module prg( in A, in B, in C, in R, out O ) 
   /*@ requires "True && emp "@*/
   /*@ ensures  "True && (R?. (A? // B? // C?).{O})^*" @*/
{
   do {
      fork {
	 await( A );
      } par {
	 await( B );
      } par {
	 await( C );
      };
      emit O();
   } every( R )
}
exports.prg = new hh.ReactiveMachine( prg, "ABCRO" );
