"use strict"

var hh = require( "hiphop" );

function func() {
   console.log( "atom works!" );
}

hiphop module prg() 
   /*@ requires emp @*/
   /*@ ensures  ({})^* @*/
   /*@ ensures  ({A, B})^* @*/
   /*@ ensures  ({A}.{B})^* @*/
{
   loop {
      yield;
      emit A;
      yield;
      emit B;
      hop { func() };
   }
}

exports.prg = new hh.ReactiveMachine( prg, "atom" );
