"use hopscript"

const hh = require( "hiphop" );

const pauseModule = module() {
   yield;
}

const m = new hh.ReactiveMachine(
   module() {
      loop {
	 hop { console.log( ">>> start" ) };
	 if( 1 ) {
	    run ${pauseModule}();
	 } else {
	    yield;
	 }
	 hop { console.log( ">>> end" ) }
      }
   } )

m.react();
setTimeout( () => m.react(), 200 );
