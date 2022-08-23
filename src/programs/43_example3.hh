"use hopscript"

var hh = require( "hiphop" );

hiphop module prg( in A, T, V ) 

   /*@ requires "True && emp" @*/
   /*@ ensures "True && ({S, !A})^* " @*/	

{

   abort( A ) {
      signal S;

      loop {
	 emit S();

	 present( S ) {emit T()};
	 
	 yield;
	 emit V();
      }
   }
}

exports.prg = new hh.ReactiveMachine( prg, "example3" );
