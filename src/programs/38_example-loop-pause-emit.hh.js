"use hopscript"

var hh = require( "hiphop" );

hiphop module prg( in I, S ) {
    /*@ requires TRUE /\ emp @*/
   /*@ ensures TRUE /\ (I.now?.S)^* @*/
   loop {
      await( I.now );
      yield;
      emit S();
   }
}

exports.prg = new hh.ReactiveMachine( prg, "looppauseemit" );
