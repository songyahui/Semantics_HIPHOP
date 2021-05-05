"use hiphop";
"use strict";

var hh = require( "hiphop" );

hiphop module prg( out T ) 

   /*@ requires "True && emp" @*/
   /*@ ensures "True && {S}  " @*/	

{

   yield;
   
      signal S;

      emit S();

      if( S.now ) {emit T()};
   
}

exports.prg = new hh.ReactiveMachine( prg, "example1" );
