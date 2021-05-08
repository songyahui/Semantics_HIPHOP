"use hiphop"
"use hopscript"

const hh = require( "hiphop" );

hiphop module prg( in X, Y, Z ) 

   /*@ requires "True && emp" @*/
   /*@ ensures "True && X?.{Z}" @*/	

{

   await( X.now );

   do {
      emit Y();
   } every (X);
   
   emit Z();
}

var m = new hh.ReactiveMachine( prg );

