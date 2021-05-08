"use hiphop";
"use hopscript";

var hh = require( "hiphop" );

hiphop module prg( J ) 

   /*@ requires "True && emp" @*/
   /*@ ensures "True && ({I}.{J} ) " @*/	

{

   signal I;
   
   fork {
      emit I();
   } par {
      await( I.now );
      emit J();
   }
}

exports.prg = new hh.ReactiveMachine( prg, "parallel" );
