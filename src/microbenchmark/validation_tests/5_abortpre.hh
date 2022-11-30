"use hiphop"
"use hopscript"

var hh = require( "hiphop" );

module prg(out O, out S ) 
   /*@ requires "True && emp" @*/
   /*@ ensures "True && ({})^*" @*/

{
   loop {
      abort( S ) {
	 emit S;
	 yield;
	 emit O;
      };
      yield;
   }
}


exports.prg = new hh.ReactiveMachine(prg, "abortpre");
