"use hiphop"
"use hopscript"

const hh = require( "hiphop" );

module prg( in X, out Y, out Z ) 

   /*@ requires "True && emp" @*/
   /*@ ensures "True && X?.(Z?.X?.{Y})^*" @*/	

{

   await( X );


   do {
      emit Y();
   } every (Z);
   

}

var m = new hh.ReactiveMachine( prg );

