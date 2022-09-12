"use hopscript"

const hh = require( "hiphop" );

hiphop module prg( out A, out B, out C ) 

   /*@ requires "True && emp" @*/
   /*@ ensures "True && (({!A} + {B})^* // ({!C} + {B})^*) " @*/	

{

   fork {
      loop {
	 present( B) {emit A()};
	 yield;
      }
   } par {
      loop {
	 present( C ) {
	    emit B( 4 );
	 } else {
	    emit B( 3 );
	 } ;
	 yield;
      }
   }
}

const m = new hh.ReactiveMachine( prg );
m.debug_emitted_func = console.log;

m.react();
m.react();
m.inputAndReact( "C" );
m.react();
m.inputAndReact( "C" );
m.inputAndReact( "C" );

