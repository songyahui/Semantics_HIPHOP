"use hiphop"
"use hopscript"

var hh = require("hiphop");

hiphop module prg( in A, in B, in C, in R, out O ) 
   /*@ requires "True && emp "@*/
   /*@ ensures  "True && ({O})^*" @*/
{
   abort (B) {
      yield;
      emit A;
      yield; 
      emit C;
      yield;
      emit R;



   }

}
exports.prg = new hh.ReactiveMachine( prg, "ABCRO" );
