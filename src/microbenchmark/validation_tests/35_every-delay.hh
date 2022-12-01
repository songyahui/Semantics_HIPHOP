"use hopscript"

var hh = require( "hiphop" );

module prg( in I, O ) 

   /*@ requires "True && emp" @*/
   /*@ ensures "True && {}.(I?.I?.{O})^* " @*/	

{
   do{
   await (I) ;
      emit O();
  
   } every (I )
}

exports.prg = new hh.ReactiveMachine( prg, "everydelay" );
