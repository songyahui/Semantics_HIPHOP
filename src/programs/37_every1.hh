"use hiphop";
"use hopscript";

const hh = require( "hiphop" );

hiphop module prg( in I, O ) {
    /*@ requires TRUE /\ emp @*/
   /*@ ensures TRUE /\ O^* @*/
    do {
      emit O();
   }every( I.now )
}

exports.prg = new hh.ReactiveMachine( prg, "every1" );
