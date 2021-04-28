"use hiphop"
"use hopscript"

const hh = require( "hiphop" );

hiphop module prg( in X, Y, Z ) 

   /*@ requires "True && emp" @*/
   /*@ ensures "True && X?.({Y}.{X})^*.{Z}" @*/	

{

   await( X.now );

   do {
      emit Y();
   } every count( X.nowval + 5, true );
   
   emit Z();
}

var m = new hh.ReactiveMachine( prg );

