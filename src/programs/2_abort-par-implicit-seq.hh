"use hiphop"
"use hopscript"

var hh = require( "hiphop" );

hiphop module prg( in I, out O )
    /*@ requires "True && emp" @*/
    /*@ ensures "True && {O}" @*/
 {
   signal L;

   fork {
      abort( L ) {
	 loop {
	    emit O;
	    yield;
	 }
      }
   } par {
      await( O );
      emit L();
   }
}

exports.prg = new hh.ReactiveMachine( prg, "abortpar" );

