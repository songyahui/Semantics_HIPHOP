"use hiphop";
"use strict";

var hh = require( "hiphop" );

module prg( out T ) 

   /*@ requires "True && emp" @*/
   /*@ ensures "True && {S}  " @*/	

{


   
      signal S;

      emit S();

      present( S ) {emit T()};
   
}

exports.prg = new hh.ReactiveMachine( prg, "example1" );
