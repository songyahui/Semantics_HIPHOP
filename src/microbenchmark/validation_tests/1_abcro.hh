"use hiphop"
"use hopscript"

var hh = require("hiphop");

hiphop module prg( in A, in B, in C, in R, out O ) 
   /*@ requires "True && emp "@*/
   /*@ ensures  "True && ((A? // B? // C?).{O})^*" @*/
{
   do {
      yield;
     emit A ;
         

   } every( R )
}
exports.prg = new hh.ReactiveMachine( prg, "ABCRO" );
