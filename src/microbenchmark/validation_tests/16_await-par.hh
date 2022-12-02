"use hiphop"
"use hopscript"


var hh = require( "hiphop" );

module prg( in A, in B, out O ) 
   /*@ requires "True && emp" @*/
   /*@ ensures "True &&  {}·(A? // B?)·{O}" @*/
{

   fork {
      await( A );
   } par {
      await( B );
   };
   emit O;
}

exports.prg = new hh.ReactiveMachine( prg, "awaitpar" );
