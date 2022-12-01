"use hopscript"

var hh = require( "hiphop" );

module example( out I, out O ) 

   /*@ requires "True && emp" @*/
   /*@ ensures "True && {}·(({O, I}·{O}) + {!O}·{O})^*" @*/	

{

   loop {
      yield;
      present( O ) {emit I()};
      yield;
      emit O();
   }
}

exports.prg = new hh.ReactiveMachine( example, "presentemit" );
