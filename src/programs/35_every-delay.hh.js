"use hopscript"

var hh = require( "hiphop" );

hiphop module prg( in I, O ) {
   /*@ requires TRUE /\ emp @*/
   /*@ ensures TRUE /\ (O)^* @*/
   do {
      emit O();
   }every count( 2, I.now )
}

exports.prg = new hh.ReactiveMachine( prg, "everydelay" );
