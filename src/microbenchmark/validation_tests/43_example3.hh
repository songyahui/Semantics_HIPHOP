"use hopscript"

var hh = require( "hiphop" );

module prg( in A, T, V ) 

   /*@ requires "True && emp" @*/
   /*@ ensures "True && ({}·({S, T, !A}·{V, !A})^*) + ({}·({S, T, !A}·{V, !A})^*·{S, T, A}) + {}·({S, T, !A}·{V, !A})^*·{S, T, !A}·{V, A} " @*/	

{

   abort( A ) {
      signal S;

      loop {
               yield;

	 emit S();

	 present( S ) {emit T()};
	 
	 yield;
	 emit V();
      }
   }
}

exports.prg = new hh.ReactiveMachine( prg, "example3" );
