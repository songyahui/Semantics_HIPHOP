"use hiphop"
"use hopscript"

const hh = require( "hiphop" );

hiphop module prg(out O ) 

   /*@ requires "True && emp" @*/
   /*@ ensures "t>3 && ({} # t).{O}" @*/	

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
