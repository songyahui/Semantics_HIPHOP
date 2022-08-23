"use hopscript"

var hh = require( "hiphop" );

hiphop module prg( in A, out T, out V ) 

   /*@ requires "True && emp" @*/
   /*@ ensures "True && ({S})^* " @*/	

{


   signal S;

   loop {
      abort( A ) {
	 emit S();
	 present( S ) {emit T()} else{};
	 yield;
	 emit V();
      }
   }
}

exports.prg = new hh.ReactiveMachine( prg, "example4" );
