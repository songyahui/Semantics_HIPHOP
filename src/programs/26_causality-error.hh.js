"use hopscript"

var hh = require( "hiphop" );

hiphop module example( I, O ) {
    /*@ requires TRUE /\ emp @*/
    /*@ ensures TRUE /\ (I.O || O)^* @*/
   loop {
      if( now( O ) ) {emit I()};
      emit O();
      yield;
   }
}

exports.prg = new hh.ReactiveMachine( example, "presentemit" );
