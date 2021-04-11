"use hiphop";
"use strict";

var hh = require( "hiphop" );

hiphop module prg( T ) {
    /*@ requires TRUE /\ emp @*/
    /*@ ensures TRUE /\ S.({} || T) @*/
   yield;
   
      signal S;

      emit S();

      if( S.now ) {emit T()};
   
}

exports.prg = new hh.ReactiveMachine( prg, "example1" );
