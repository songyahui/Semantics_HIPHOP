"use hopscript"

var hh = require( "hiphop" );

hiphop module prg( O ) {
    /*@ requires TRUE /\ emp @*/
    /*@ ensures TRUE /\ (O.O)^* @*/
   loop {
      emit O( 5 );
      yield;
      emit O();
   }
}

exports.prg = new hh.ReactiveMachine( prg, "emitnovalue" );
