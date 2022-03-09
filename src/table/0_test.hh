"use hiphop"
"use hopscript"

var hh = require("hiphop");

hiphop module prg(out Start, in A, in B, in C, in D, out O, out Done ) 
   /*@ requires "True && emp "@*/
   /*@ ensures  "True && ({})^*.{A}" @*/
{
   emit Start();
   yield;
   emit B ();
   //async Done {
      emit A();
      if (B.now) {yield; emit C()}
      else {yield; emit D()};
      
      
   //};
   
}

exports.prg = new hh.ReactiveMachine( prg, "ABCRO" );