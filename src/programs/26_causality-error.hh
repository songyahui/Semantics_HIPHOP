"use hopscript"

var hh = require( "hiphop" );

hiphop module example( out I, in O ) 

   /*@ requires "True && emp" @*/
   /*@ ensures "True && {O}.{O}^*" @*/	

{

   loop {
      present( now( O ) ) {emit I()};
      emit O();
      yield;
   }
}

exports.prg = new hh.ReactiveMachine( example, "presentemit" );
