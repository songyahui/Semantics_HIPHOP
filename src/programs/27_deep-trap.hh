"use hopscript"

const hh = require( "hiphop" );

hiphop module prg() 

   /*@ requires "True && emp" @*/
   /*@ ensures "True && emp" @*/	

{
// currently trap has not fully implemented. 
   trap {
      trap {
	 exit 2;
      };
      hop { console.log( "first level" ) };
   };
   hop { console.log( "top level" ) };
}

var m = new hh.ReactiveMachine( prg );

m.react();
