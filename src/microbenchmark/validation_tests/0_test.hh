"use hiphop"
"use hopscript"

var hh = require("hiphop");

module prg( in A, in B, in C, in R, out O ) 
   /*@ requires "True && emp "@*/
   /*@ ensures  "True && {} . (A? // B? // C?).{R}" @*/
      /*@ ensures  "True && {} . (A? // B? // C?)" @*/

{
      fork {
	 await( A );
      } par {
	 await( B );
      } par {
	 await( C );
      };
      yield;
      emit R;

}
exports.prg = new hh.ReactiveMachine( prg, "ABCRO" );
