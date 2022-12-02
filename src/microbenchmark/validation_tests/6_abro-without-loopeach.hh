"use hopscript"

var hh = require("hiphop");

module prg( in A, in B, in R, out O ) 
   /*@ requires "True && emp" @*/
   /*@ ensures "True && {}·(({A, !S}·{O, !S, I, K}) + ({A, !S}·{O, !S, !I}) + ({A, S, I, K}) + ({A, S, !I}) + ({A, !S}·{O, S, I, K}) + {A, !S}·{O, S, !I})^*" @*/
      /*@ ensures "True && {}·(({A, !S}·{O, !S, I, K}) + ({A, !S}·{O, !S, !I}) + ({A, S, I, K}) + ({A, S, !I}) + ({A, !S}·{O, S, I, K}) + {A, !S}·{O, S, !I})" @*/

{

   loop {
      abort( S ) {
   yield;
	 emit A;
	 yield;
	 emit O;
      };
	        present( I ) {
	 emit K;
      }
   }
}

exports.prg = new hh.ReactiveMachine( prg, "ABRO" );


