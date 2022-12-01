"use hiphop"
"use hopscript"

var hh = require( "hiphop" );

module prg( in I, out O ) 
   /*@ requires "True && emp" @*/
   /*@ ensures "True && {}·(I?·I?·I?·{O})^*" @*/
{

   loop {
      await I;
      await I;
      await I;
      emit O();
   }
}

exports.prg = new hh.ReactiveMachine( prg, "await3" );
