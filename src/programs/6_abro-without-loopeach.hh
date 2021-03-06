"use hopscript"

var hh = require("hiphop");

hiphop module prg( in A, in B, in R, out O ) 
   /*@ requires "True && emp" @*/
   /*@ ensures "True && (A? // B?·{O, !R})^*" @*/
{

   loop {
      abort( R.now ) {
	 fork {
	    await( A.now );
	 } par {
	    await( B.now );
	 };
	 emit O();
	 halt;
      }
   }
}

exports.prg = new hh.ReactiveMachine( prg, "ABRO" );


