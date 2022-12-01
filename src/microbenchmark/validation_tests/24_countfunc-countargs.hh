"use hiphop"
"use hopscript"

const hh = require( "hiphop" );

module prg( in X, out Y, out Z ) 

   /*@ requires "True && emp" @*/
   /*@ ensures "True && {}·X?·Z?·(({Y, !Z}·({!Z})^*) + ({Y, Z}) + {Y, !Z}·({!Z})^*·{Z})^*" @*/	

{

   await( X );


   do {
      yield;
      emit Y();
   } every (Z);
   

}

var m = new hh.ReactiveMachine( prg );

