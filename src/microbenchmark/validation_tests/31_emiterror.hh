"use hopscript"

const hh = require( "hiphop" );

module prg( out O ) 

   /*@ requires "True && emp" @*/
   /*@ ensures "True &&  {}·({O(5)}·{})^* " @*/	
      /*@ ensures "True &&  {}·({O(5)}·{})" @*/	


{

   loop {
      yield;
      emit O( 5 );
      emit O( 5 );
      yield;
   }
}

const machine = new hh.ReactiveMachine( prg, "emiterror" );

