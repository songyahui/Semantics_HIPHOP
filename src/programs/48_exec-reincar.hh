"use hiphop"
"use hopscript"

const hh = require( "hiphop" );

var glob = 5;

hiphop module prg( in R, in O, in OT, in T ) 

   /*@ requires "True && emp" @*/
   /*@ ensures "t>1 && (R?.({!R} # t).{T, !R})^* " @*/	

{

   do {
      fork {
	 abort( R.now ) {
	    async T {
	       console.log( "Oi." );
	       setTimeout( function( self ) {
		  console.log( "Oi timeout." );
		  self.notify( glob++ , false );
		 }, 1000, this);
	    }
	 };
	 emit OT( T.nowval);
      } par {
	 emit O();
      }
   } every( R.now )
}

var machine = new hh.ReactiveMachine( prg, "exec" );
machine.debug_emitted_func = console.log;

machine.react();
