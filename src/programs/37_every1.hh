"use hiphop";
"use hopscript";

const hh = require( "hiphop" );

hiphop module prg( in I, out O ) 

   /*@ requires "True && emp" @*/
   /*@ ensures "True && (I?.{O})^* " @*/	

{

    do {
      emit O();
   }every( I.now )
}

exports.prg = new hh.ReactiveMachine( prg, "every1" );
