"use hiphop";
"use hopscript";

var hh = require( "hiphop" );

module prg( J ) 

   /*@ requires "True && emp" @*/
   /*@ ensures "True && {I}·I?·{J} " @*/	

{

   signal I;
   
   fork {
      emit I();
   } par {
      await( I );
      emit J();
   }
}

exports.prg = new hh.ReactiveMachine( prg, "parallel" );
