"use hopscript"

var hh = require( "hiphop" );

hiphop module prg( in A, in B, out O ) 
   /*@ requires "True && emp" @*/
   /*@ ensures "True && (A?. B?).{O}" @*/
{

   await( A );
   await( B );
   emit O;
}

exports.prg = new hh.ReactiveMachine( prg, "awaitseq" );
