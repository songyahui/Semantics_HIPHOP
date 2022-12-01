"use hiphop"
"use hopscript"

var hh = require("hiphop");

module prg( in A, in B, in C, in AA, in BB, in CC, in R, out O ) 
   /*@ requires "True && emp "@*/
   /*@ ensures  "True && ({}·{A, C, !S}·{R, !S}) + ({}·{A, C, S}) + ({}·{A, C, !S}·{R, S}) + ({}·{!A, CC, !S}·{BB, !S}) + ({}·{!A, CC, S}) + {}·{!A, CC, !S}·{BB, S}" @*/
{
   abort (S) {
      yield;
      present (A){
         emit C;
      yield;
      emit R;
      }
       else {
         emit CC;
      yield;
      emit BB;
      }
   }

}
exports.prg = new hh.ReactiveMachine( prg, "ABCRO" );
