"use hiphop"
"use hopscript"

const hh = require( "hiphop" );

hiphop module prg( in X, out Y, out Z ) 

   /*@ requires "True && emp" @*/
   /*@ ensures "True && X?.(Z?.X?.{Y})^*" @*/	

{

   await( X.now );


   do {
      emit Y();
   } every (Z.now);
   

}

var m = new hh.ReactiveMachine( prg );

