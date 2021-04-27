"use hopscript"

var hh = require( "hiphop" );

hiphop module prg( J ) {
    /*@ requires TRUE /\ emp @*/
   /*@ ensures TRUE /\ ( (J || {} )|| I) @*/
   signal I;
   
   fork {
      if( I.now ) {emit J()};
   } par {
      emit I();
   }
}

exports.prg = new hh.ReactiveMachine( prg, "parallel2" );
