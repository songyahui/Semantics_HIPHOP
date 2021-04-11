"use hiphop"
"use hopscript"


var hh = require( "hiphop" );

hiphop module prg( in A, in B, out O ) {
    /*@ requires TRUE /\ emp @*/
    /*@ ensures TRUE /\ (A? || B?).{O} @*/
   fork {
      await( A.now );
   } par {
      await( B.now );
   };
   emit O();
}

exports.prg = new hh.ReactiveMachine( prg, "awaitpar" );
