"use hiphop"
"use hopscript"

var hh = require("hiphop");

hiphop module prg(out Start, in A, in B, in C, in R, out O, out Done ) 
   /*@ requires "True && emp "@*/
   /*@ ensures  "True && ({})^*.{A}" @*/
{
   emit Start();
   pause;
   async Done {
      emit A();
      
      if (B.now) {
          emit C();
      }
      else {emit D()};
      pause;
   };
   emit B ()
}

exports.prg = new hh.ReactiveMachine( prg, "ABCRO" );