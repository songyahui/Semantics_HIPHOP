"use hiphop"
"use hopscript"

var hh = require( "hiphop" );

module prg(out O, out S ) 
   /*@ requires "True && emp" @*/
   /*@ ensures "True && ({})^*" @*/

{
   loop {
      abort( S ) {
   yield;
	 emit A;
	 yield;
	 emit O;
      };
   }
}


exports.prg = new hh.ReactiveMachine(prg, "abortpre");
