"use hopscript"

const hh = require( "hiphop" );

module setTimeout () 
/*@ requires "True && {}^*" @*/
/*@ ensures "True && {}" @*/	
/*@ ensures "True && emp" @*/	

{
   ();
}

module prg( in T, in O, in OT ) 

   /*@ requires "True && emp" @*/
   /*@ ensures "True && {O, OT}·{}·{T} " @*/	
      /*@ ensures "True && {O, OT}·{}" @*/	


{

   fork {
      async T {
	 console.log( "Oi." );
	 setTimeout( function( self ) {
	    console.log( "Oi timeout." );
	    self.notify( 5, false );
	 }, 3000, this );
      };
      emit OT();
   } par {
      emit O();
   }
}

var machine = new hh.ReactiveMachine( prg, "exec" );
machine.debug_emitted_func = console.log;


