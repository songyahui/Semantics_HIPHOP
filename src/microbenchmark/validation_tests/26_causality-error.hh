"use hopscript"

var hh = require( "hiphop" );

module example( out I, in O ) 

   /*@ requires "True && emp" @*/
   /*@ ensures "True && {}·(({now(O), I, O}·{}) + {!now(O), O}·{})^*" @*/	
      /*@ ensures "True && {}·(({now(O), I, O}·{}) + {now(O), O}·{})^*" @*/	


{

   loop {
      yield;
      present( now( O ) ) {emit I()};
      emit O();
      yield;
   }
}

exports.prg = new hh.ReactiveMachine( example, "presentemit" );
