"use hopscript"

var hh = require( "hiphop" );

hiphop module example( out I, out O ) 

   /*@ requires "True && emp" @*/
   /*@ ensures "True && ({I, O}.{I, O}^*) + {!O}.{I, O}^*" @*/	

{

   loop {
      present( O ) {emit I()};
      yield;
      emit O();
   }
}

exports.prg = new hh.ReactiveMachine( example, "presentemit" );
