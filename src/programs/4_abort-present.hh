"use hopscript"

var hh = require( "hiphop" );

hiphop module prg
   ( in I, out J, 
     out K, out V ) {
       /*@ requires TRUE /\ emp @*/
       /*@ ensures TRUE /\ (J.V || K)^* @*/
   loop {
      abort( I.now ) {
	 emit J();
	 yield;
	 emit V();
	 yield;
      };
      if( I.now ) {
	 emit K();
      }
   }
}

exports.prg = new hh.ReactiveMachine( prg, "abortpresent" );
