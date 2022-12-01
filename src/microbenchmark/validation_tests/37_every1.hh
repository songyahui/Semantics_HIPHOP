"use hiphop";
"use hopscript";

const hh = require( "hiphop" );

module prg( in I, out O ) 

   /*@ requires "True && emp" @*/
   /*@ ensures "True && I?.{O}. (I?.{O})^* " @*/	

{

    do {
      yield;
      emit O();
      
   }every( I )
}

exports.prg = new hh.ReactiveMachine( prg, "every1" );
