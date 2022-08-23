"use hopscript"

var hh = require("hiphop");

hiphop module prg( in A, in B, in R, out O ) 
   /*@ requires "True && emp" @*/
   /*@ ensures "True && (A? // B?·{O, !R})^*" @*/
{

   loop {
      abort( R ) {
	 fork {
	    await( A );
	 } par {
	    await( B );
	 };
	 emit O;
	 halt;
      }
   }
}

exports.prg = new hh.ReactiveMachine( prg, "ABRO" );


