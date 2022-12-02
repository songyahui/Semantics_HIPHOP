"use hopscript"

var hh = require( "hiphop" );

module prg( in A, out T, out V ) 

   /*@ requires "True && emp" @*/
   /*@ ensures "True && {}·(({}·{S, T, !A}·{V, !A}) + ({}·{S, T, A}) + {}·{S, T, !A}·{V, A})^* " @*/	
      /*@ ensures "True && {}·(({}·{S, T, !A}·{V, !A}) + ({}·{S, T, A}) + {}·{S, T, !A}·{V, A}) " @*/	


{


   signal S;

   loop {
      yield;
      abort( A ) {
          yield;
	 emit S();
	 present( S ) {emit T()} else{};
	 yield;
	 emit V();
      }
   }
}

exports.prg = new hh.ReactiveMachine( prg, "example4" );
