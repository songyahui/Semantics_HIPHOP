"use hopscript"

var hh = require( "hiphop" );

hiphop module prg( in I, out S ) 

   /*@ requires "True && emp" @*/
   /*@ ensures "True && I?.({S}.I?)﹡^* " @*/	

{

   loop {
      await( I.now );
      yield;
      emit S();
   }
}

exports.prg = new hh.ReactiveMachine( prg, "looppauseemit" );
