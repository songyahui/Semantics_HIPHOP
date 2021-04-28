"use hopscript"

var hh = require( "hiphop" );

hiphop module prg( in I, S ) 

   /*@ requires "True && emp" @*/
   /*@ ensures "True && (I?.{S})^* " @*/	

{

   loop {
      await( I.now );
      yield;
      emit S();
   }
}

exports.prg = new hh.ReactiveMachine( prg, "looppauseemit" );
