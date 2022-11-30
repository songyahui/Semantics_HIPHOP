"use hopscript"

var hh = require( "hiphop" );

module prg
   ( in I, out J, 
     out K, out V ) 
     
   /*@ requires "True && emp" @*/
   /*@ ensures "True && ({!I, J, K}.{!I, V})^* + ({!I, J}.{!I, V})^*" @*/
{

   loop {
      abort( I ) {
	 emit J;
	 yield;
	 emit V;
	 yield;
      };
      present( I ) {
	 emit K;
      }
   }
}

exports.prg = new hh.ReactiveMachine( prg, "abortpresent" );
