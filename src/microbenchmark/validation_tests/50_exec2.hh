"use hiphop"
"use hopscript"

const hh = require( "hiphop" );

module setTimeout () 
/*@ requires "True && {}^*" @*/
/*@ ensures "True && {}" @*/	
/*@ ensures "True && S?" @*/	


{
   ();
}

module prg(out O ) 

   /*@ requires "True && emp" @*/
   /*@ ensures "True && {}·{}·{O}" @*/	
      /*@ ensures "True && {}·{}·{!O}" @*/	


{
   async O {
      setTimeout( () => this.notify( 5 ), 3000 );
   };
}

var machine = new hh.ReactiveMachine( prg, "exec" );

machine.addEventListener( "O", function( evt ) {
   console.log( "O emitted!" );
} );

machine.react();
