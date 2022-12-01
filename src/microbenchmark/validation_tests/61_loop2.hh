"use hiphop"
"use hopscript"

var hh = require("hiphop");

module prg( in A, in B, in C, in R, out O ) 
   /*@ requires "True && emp "@*/
   /*@ ensures  "True && {}·({A}·{C}·{R}·{})^*·{}" @*/
{
        
      loop{
          yield;
         emit A;
      yield; 
      emit C;
      yield;
      emit R;
            yield;
      };
       yield;      

}
exports.prg = new hh.ReactiveMachine( prg, "ABCRO" );
