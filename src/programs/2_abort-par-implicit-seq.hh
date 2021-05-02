"use hiphop"
"use hopscript"

var hh = require( "hiphop" );

hiphop module prg( in I, out O )
    /*@ requires "True && emp" @*/
    /*@ ensures "True && {}.{I}.{I, L}. ({I}^*)" @*/
 {
   signal L;

   fork {
      yield;
	 loop {
	    emit I();
	    yield;
	 }
  //    }
   } par {
      await( I.now );
      emit L();
   }
}

exports.prg = new hh.ReactiveMachine( prg, "abortpar" );
