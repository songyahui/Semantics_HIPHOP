"use hopscript"

var hh = require( "hiphop" );

hiphop module prg( in A, T, V ) 

   /*@ requires "True && emp" @*/
   /*@ ensures "True && ({S, !A})^* " @*/	

{

   abort( A.now ) {
      signal S;

      loop {
	 emit S();

	 if( S.now ) {emit T()};
	 
	 yield;
	 emit V();
      }
   }
}

exports.prg = new hh.ReactiveMachine( prg, "example3" );
