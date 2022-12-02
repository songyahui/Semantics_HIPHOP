"use hopscript"

const hh = require( "hiphop" );

module setTimeout () 
/*@ requires "True && {}^*" @*/
/*@ ensures "True && {}" @*/	{
   ();
}

module prg( O, OT ) 

   /*@ requires "True && emp" @*/
   /*@ ensures "True && {O}·{}·{OT}" @*/	
   
{

   fork {
      
      async OT{
         yield;
	 console.log( "Oi." );
	 setTimeout( () => {
	    console.log( "Oi timeout." );
	    this.notify( 5, false );
	 }, 3000 );
      };
   } par {
      emit O();
   }
}

var machine = new hh.ReactiveMachine( prg, "exec" );
machine.debug_emitted_func = console.log;

machine.react();
machine.react();
machine.react();
console.log( "......." );


