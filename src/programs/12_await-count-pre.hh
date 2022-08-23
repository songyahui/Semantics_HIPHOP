"use hopscript"

var hh = require( "hiphop" );

hiphop module prg( in I, out O ) 
   /*@ requires "True && emp" @*/
   /*@ ensures "True && I?.I?.I?.(({O}.I?.I?.I?)^*)" @*/

{

   loop {
      await count( 3, I );
      emit O;
   }
}

exports.prg = new hh.ReactiveMachine( prg, "await3" );
