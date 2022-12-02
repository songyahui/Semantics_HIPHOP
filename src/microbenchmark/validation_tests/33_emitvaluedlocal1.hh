"use hopscript"

var hh = require( "hiphop" );

module prg( out O ) 

   /*@ requires "True && emp" @*/
   /*@ ensures "True && {}·({S, O}·{O}·{})^*" @*/	
      /*@ ensures "True && {}·({S, O}·{O}·{})" @*/	


{

   loop {
      yield;
      signal S ;//= 1;
      
      emit S(   );
      emit O(  );
      yield;
      emit O(  );
      yield;
   }
}

exports.prg = new hh.ReactiveMachine( prg, "emitvaluedlocal1" );
