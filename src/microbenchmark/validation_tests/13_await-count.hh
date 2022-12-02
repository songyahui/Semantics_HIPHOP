"use hiphop"
"use hopscript"

const hh = require( "hiphop" );

module prg( in Tick, out O ) 
   /*@ requires "True && emp" @*/
   /*@ ensures "True && {}·(Tick?·Tick?·Tick?·{O})^*" @*/
      /*@ ensures "True && {}·(Tick?·Tick?·Tick?·{O})" @*/

{

   loop {
      await Tick;
            await Tick;
      await Tick;

      emit O();
   }
}

exports.prg = new hh.ReactiveMachine( prg, "await3" );
