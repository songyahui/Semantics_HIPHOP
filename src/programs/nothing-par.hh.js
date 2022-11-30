"use hopscript"

var hh = require( "hiphop" );

module prg() {
   fork {
      yield;
   } par {
   }
}

exports.prg = new hh.ReactiveMachine( prg, "nothingpar" );
