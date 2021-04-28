"use hiphop"
"use hopscript"

const hh = require("hiphop");

hiphop module prg(out A ) 
   /*@ requires "True && emp" @*/
   /*@ ensures "True && ({A}^* //{A}^*)//{O}^*" @*/
{

   fork {
      loop {
	 emit A( 0 );
	 yield;
      }
   } par {
      loop {
	 emit A( 1 );
	 yield;
      }
   } par {
      loop {
	 emit A( 2 );
	 yield;
      }
   }
}

let machine = new hh.ReactiveMachine( prg, "error2" );
