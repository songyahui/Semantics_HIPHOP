"use hopscript"

var hh = require( "hiphop" );

hiphop module prg( in I, out O ) {
    /*@ requires TRUE /\ emp @*/
    /*@ ensures TRUE /\ (I.pre?.{O})^* @*/
   loop {
      await count( 3, I.pre );
      emit O();
   }
}

exports.prg = new hh.ReactiveMachine( prg, "await3" );
