"use hiphop"
"use hopscript"

var hh = require("hiphop");

module prg( in A, in B, in C, in R, out O ) 
   /*@ requires "True && emp "@*/
   /*@ ensures  "True && 
     {A, !B}·({C, !B}·{A, !B})^* 
   + {A, B} 
   + {A, !B}·({C, !B}·{A, !B})^*·{C, B} 
   + {A, !B}·({C, !B}·{A, !B})^*·{C, !B}·{A, B} " @*/
{
   abort (B) {
      loop{
            yield;
         emit A;
      yield; 
      emit C;
      }
   }

}
exports.prg = new hh.ReactiveMachine( prg, "ABCRO" );
