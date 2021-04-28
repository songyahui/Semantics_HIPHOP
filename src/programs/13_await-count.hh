"use hiphop"
"use hopscript"

const hh = require( "hiphop" );

hiphop module prg( in I, out O ) 
   /*@ requires "True && emp" @*/
   /*@ ensures "True && ({I}.{O})^*" @*/
{

   loop {
      await count( 3, I.now );
      emit O();
   }
}

exports.prg = new hh.ReactiveMachine( prg, "await3" );
