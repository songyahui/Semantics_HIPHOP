"use hiphop"
"use hopscript"

var hh = require( "hiphop" );

module prg( in I, out O )
    /*@ requires "True && emp" @*/
    /*@ ensures "True && ({}·({O, !L})^*) + {}·({O, !L})^*·{O, L}" @*/
        /*@ ensures "True && (({O, !L})^*) + {}·({O, !L})^*·{O, L}" @*/

 {
   signal L;
   abort( L ) {
	 loop {
       yield;
	    emit O;
	   
	 }
      }

  
}

exports.prg = new hh.ReactiveMachine( prg, "abortpar" );
