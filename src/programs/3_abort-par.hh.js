"use hiphop"
"use hopscript"

var hh = require( "hiphop" );

hiphop module prg( in I, out O ) {
   /*@ requires TRUE /\ emp @*/
   /*@ ensures TRUE /\ O^* || I.now?.L @*/
   signal L;
   
   fork {
      abort( L.now ) {
	 loop {
	    emit O();
	    yield;
	 }
      }
   } par {
      await( I.now );
      emit L();
   }
}

exports.prg = new hh.ReactiveMachine( prg, "abortpar" );
