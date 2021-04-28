"use hopscript"

var hh = require( "hiphop" );

hiphop module prg( in I, out O ) 
   /*@ requires "True && emp" @*/
   /*@ ensures "True && ({I}.{O})^*" @*/

{
   loop {
      await immediate( I.now );
      emit O();
      yield;
   }
}

exports.prg = new hh.ReactiveMachine( prg, "awaitimmediate" );
