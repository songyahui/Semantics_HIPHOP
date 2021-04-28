"use hiphop"
"use hopscript"

const hh = require( "hiphop" );

hiphop module prg( in A, in B, in R, out O ) 
   /*@ requires "True && emp" @*/
   /*@ ensures "True && (({A}//{B}).{O})^*" @*/
{

   do {
      fork {
	 await( A.now );
      } par {
	 await( B.now );
      };
      emit O();
   } every( R.now )
}

exports.prg = new hh.ReactiveMachine( prg, "ABRO" );
