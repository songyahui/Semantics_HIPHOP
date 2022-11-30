"use hiphop"
"use hopscript"

var hh = require("hiphop");

module prg( in A, in B, in C, in R, out O ) 
   /*@ requires "True && emp "@*/
   /*@ ensures  "True && ({A, !R}·({!R})^*·({!R}·{A, !R}·({!R})^*)^*·{!R}) + ({A, !R}·({!R})^*·({!R})^*·{A, R}) + ({A, !R}·({!R})^*·({!R}·{A, !R}·({!R})^*)^*·{R}) + ({!R}) + ({A, R}) + ({R}) + ({A, !R}·({!R})^*·{!R}) + ({A, !R}·({!R})^*·{R}) + ({A, !R}·({!R})^*·{A, R}) + {A, !R}·({!R})^*·{R}" @*/
{
   do {
      yield;
     emit A ;
         

   } every( R )
}
exports.prg = new hh.ReactiveMachine( prg, "ABCRO" );
