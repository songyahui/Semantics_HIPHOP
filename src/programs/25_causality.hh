"use hopscript"

var hh = require( "hiphop" );

hiphop module example( I, O ) 

   /*@ requires "True && emp" @*/
   /*@ ensures "True && ({I}.{O})//{O}" @*/	

{

   loop {
      if( O.now ) {emit I()};
      yield;
      emit O();
   }
}

exports.prg = new hh.ReactiveMachine( example, "presentemit" );
