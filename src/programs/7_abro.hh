"use hiphop"
"use hopscript"

const hh = require( "hiphop" );

hiphop module prg( in A, in B, in R, out O ) {
    /*@ requires TRUE /\ emp @*/
    /*@ ensures TRUE /\ ((A.now? || B.now?).O)^* @*/
   do {
      fork {
	 await( A.now );
      } par {
	 await( B.now );
      };
      emit O();
   } every( R.now )
}

exports.prg = new hh.ReactiveMachine( prg, "ABRO" );
