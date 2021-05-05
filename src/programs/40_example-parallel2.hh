"use hopscript"

var hh = require( "hiphop" );

hiphop module prg( out J ) 

   /*@ requires "True && emp" @*/
   /*@ ensures "True && ({I, J} ) " @*/	

{

   signal I;
   
   fork {
      if( I.now ) {emit J()};
   } par {
      emit I();
   }
}

exports.prg = new hh.ReactiveMachine( prg, "parallel2" );
