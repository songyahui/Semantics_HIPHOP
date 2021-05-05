"use hopscript"

var hh = require( "hiphop" );

hiphop module prg( in I, O ) 

   /*@ requires "True && emp" @*/
   /*@ ensures "True && (I?.I?.{O})^* " @*/	

{
   do{
   await (I.now) ;
      emit O();
  
   } every (I.now )
}

exports.prg = new hh.ReactiveMachine( prg, "everydelay" );
