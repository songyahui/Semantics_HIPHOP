"use hopscript"

const hh = require( "hiphop" );

hiphop module prg( O ) {
    /*@ requires TRUE /\ emp @*/
    /*@ ensures TRUE /\ (O.O)^* @*/
   loop {
      emit O( 5 );
      emit O( 5 );
      yield;
   }
}

const machine = new hh.ReactiveMachine( prg, "emiterror" );

try {
   machine.react();
} catch( e ) {
   console.log( e.message );
}
