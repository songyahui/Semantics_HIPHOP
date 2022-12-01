"use hiphop"
"use hopscript"

var hh = require("hiphop");

module prg( in A, in B, in C, in R, out O ) 
   /*@ requires "True && emp "@*/
   /*@ ensures  "True && 
   ({}·{A, !B}·{C, !B}·{R, !B}) + 
   ({}·{A, !B}·{C, !B}·{B}·{R, !B}) + 
   ({}·{A, !B}·{B}·{C, !B}·{R, !B}) + 
   ({}·{A, !B}·{B}·{C, !B}·{B}·{R, !B}) + 
   ({}·{B}·{A, !B}·{C, !B}·{R, !B}) + 
   ({}·{B}·{A, !B}·{C, !B}·{B}·{R, !B}) + 
   ({}·{B}·{A, !B}·{B}·{C, !B}·{R, !B}) + 
    {}·{B}·{A, !B}·{B}·{C, !B}·{B}·{R, !B}" @*/
{
   suspend (B) {
      yield;
      emit A;
      yield; 
      emit C;
      yield;
      emit R;
   }

}
exports.prg = new hh.ReactiveMachine( prg, "ABCRO" );
