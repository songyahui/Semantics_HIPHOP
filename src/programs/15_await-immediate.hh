"use hopscript"

var hh = require( "hiphop" );

hiphop module prg( in I, out O ) 
   /*@ requires "True && emp" @*/
   /*@ ensures "True && I?.{O}.({}.I?.{O})^*" @*/

{
   loop {
      await ( I );
      emit O;
      yield;
   }
}

exports.prg = new hh.ReactiveMachine( prg, "awaitimmediate" );
