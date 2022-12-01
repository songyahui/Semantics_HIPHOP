"use hopscript"

const hh = require( "hiphop" );

module prg( out A, out B, out C ) 

   /*@ requires "True && emp" @*/
   /*@ ensures "True && ({}·{A, B, B(4), C}·{}·{A, B, B(4), C}·{}·{A, B, B(4), C}·{}) + ({}·{A, B, B(4), C}·{}·{A, B, B(4), C}·{}·{A, B, B(3), !C}) + ({}·{A, B, B(4), C}·{}·{A, B, B(4), C}·{}·{B(4), C, !B}) + ({}·{A, B, B(4), C}·{}·{A, B, B(4), C}·{}·{B(3), !B, !C}) + ({}·{A, B, B(4), C}·{}·{A, B, B(3), !C}) + ({}·{A, B, B(4), C}·{}·{B(4), C, !B}) + ({}·{A, B, B(4), C}·{}·{B(3), !B, !C}) + ({}·{A, B, B(3), !C}) + ({}·{B(4), C, !B}) + {}·{B(3), !B, !C} " @*/	

{

   fork {
      loop {
         yield;
	 present( B) {emit A()};
	 yield;
      }
   } par {
      loop {
           yield;
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

