"use hopscript"

var hh = require( "hiphop" );

module prg
   ( in I, out J, 
     out K, out V ) 
     
   /*@ requires "True && emp" @*/
   /*@ ensures "True && ({}·{J, !I}·{V, !I}) + ({}·{J, I, K}) + {}·{J, !I}·{V, I, K}" @*/
      /*@ ensures "True && ({}·{J, !I}·{V, !I}) + {}·{J, !I}·{V, I, K}" @*/

{

    abort( I ) {
    yield;
	 emit J;
	 yield;
	 emit V;
      };
      present( I ) {
	 emit K;
      }
}

exports.prg = new hh.ReactiveMachine( prg, "abortpresent" );
