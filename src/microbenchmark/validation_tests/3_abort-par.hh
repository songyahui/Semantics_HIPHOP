"use hiphop"
"use hopscript"

var hh = require( "hiphop" );


module prg( in I, out O ) 
   /*@ requires "True && emp" @*/
    /*@ ensures "True && ({}·{O, !L}·{L, O}) + {}·{O, L}·{L}" @*/
{
   signal L;
   
   fork {
      abort( L ) {
	 loop {
       yield;
	    emit O;
	   
	 }
      }
   } par {
      await( O );
      emit L;
   }
}

exports.prg = new hh.ReactiveMachine( prg, "abortpar" );

// ({}·({O, !L})^*) + {}·({O, !L})^*·{O, L}