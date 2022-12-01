"use hiphop"
"use hopscript"

const hh = require("hiphop");

module prg(out A, out B, out C ) 
   /*@ requires "True && emp" @*/
   /*@ ensures "True && {A(0), B(1), C(2)}·{}" @*/
{

   fork {
     // loop {
	 emit A( 0 );
	 yield;
    //  }
   } par {
    //  loop {
	 emit B( 1 );
	 yield;
    //  }
   } par {
    //  loop {
	 emit C( 2 );
	 yield;
    //  }
   }
}

let machine = new hh.ReactiveMachine( prg, "error2" );
