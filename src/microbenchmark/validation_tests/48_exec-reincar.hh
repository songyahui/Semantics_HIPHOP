"use hiphop"
"use hopscript"

const hh = require( "hiphop" );

var glob = 5;

module setTimeout () 
/*@ requires "True && {}^*" @*/
/*@ ensures "True && {}" @*/
/*@ ensures "True && {!B}" @*/	

{
   ();
}

module prg( in R, in O, in OT, in T ) 

   /*@ requires "True && emp" @*/
   /*@ ensures "True && ({}·{O}·{!R}·{OT, T, !R}) + ({}·{O}·{OT, R}) + {} " @*/	
   /*@ ensures "True && ({}·{O}·{!R}·{OT, T, !R}) + ({}·{O}·{OT, R}) " @*/	

{

   
	yield;
      fork {
	 abort( R ) {
	    async T {
	       console.log( "Oi." );
	       setTimeout( () => {
		  console.log( "Oi timeout." );
		  self.notify( glob , false );
		 }, 1000, this);
	    };
	 };
	 emit OT();
      } par {
	 emit O();
      }
   
}

var machine = new hh.ReactiveMachine( prg, "exec" );
machine.debug_emitted_func = console.log;

machine.react();
