"use hopscript"

var hh = require( "hiphop" );

hiphop module prg( in I, O ) {
   do {
      emit O();
   }every immediate( I.now )
}

exports.prg = new hh.ReactiveMachine( prg, "everyimmediate" );
