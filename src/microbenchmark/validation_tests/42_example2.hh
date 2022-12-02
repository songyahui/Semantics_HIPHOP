"use hopscript"

var hh = require( "hiphop" );

module prg( T, V ) 

   /*@ requires "True && emp" @*/
   /*@ ensures "True && {}·({S, T}·{V})^* " @*/	
      /*@ ensures "True && {}·({ST}·{V})^* " @*/	


{

   signal S;

   loop {
      yield;
      emit S();
      present( S ) {emit T()};
      yield;
      emit V();
   }
}

exports.prg = new hh.ReactiveMachine( prg, "example2" );
