"use hopscript"

var hh = require( "hiphop" );

module m( in S, O, F, W ) {
   weakabort( S.now ) {
      loop {
	 emit O();
	 yield;
	 emit W();
      }
   }
   emit F();
}

exports.prg = new hh.ReactiveMachine( m, "wabort" );
