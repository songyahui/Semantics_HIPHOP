"use strict"

var hh = require("hiphop");

module prg() 
   /*@ requires "True && emp" @*/
   /*@ ensures "True && {}·({L()}·{})^*" @*/
{

   loop {
      yield;
      signal L;

      emit L();
      yield;
      hop { console.log( "atom works! value of L is", L.nowval ) }
   }
}

exports.prg = new hh.ReactiveMachine(prg, "atom");
