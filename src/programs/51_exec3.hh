"use hiphop"
"use hopscript"

const hh = require( "hiphop" );

hiphop module prg( out O ) 

   /*@ requires "True && emp" @*/
   /*@ ensures "t>1 && ({} # t).{O}" @*/	

{

   async O {
      this.notify( new Promise( function( resolve, reject ) {
	 setTimeout( () => resolve( 5 ), 1000 );
      } ) );
   }
}

var machine = new hh.ReactiveMachine( prg, "exec" );

machine.addEventListener( "O", function( evt ) {
   console.log( "O=" + evt.nowval.val + " emitted!" );
} );

machine.react();
