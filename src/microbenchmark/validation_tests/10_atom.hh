"use strict"

var hh = require( "hiphop" );

function func() {
   console.log( "atom works!" );
}

module prg(out A, out B) 
   /*@ requires "True && emp" @*/
   /*@ ensures "True && {}·({A}·{B})^*" @*/
      /*@ ensures "True && {}·({A}·{B})" @*/

{
   loop {
      yield;
      emit A ();
      yield;
      emit B ();
      hop { func() };
   }
}

exports.prg = new hh.ReactiveMachine( prg, "atom" );
