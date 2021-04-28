"use strict"

var hh = require( "hiphop" );

function func() {
   console.log( "atom works!" );
}

hiphop module prg() 
   /*@ requires "True && emp" @*/
   /*@ ensures "True && ({A}.{B})^*" @*/
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
