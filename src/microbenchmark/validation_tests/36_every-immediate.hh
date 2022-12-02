"use hopscript"

var hh = require( "hiphop" );

module prg( in I, O ) 

   /*@ requires "True && emp" @*/
   /*@ ensures "True &&  {}·I?·(({O, !I}·({!I})^*) + 
   ({O, I}) + {O, !I}·({!I})^*·{I})^* " @*/	

      /*@ ensures "True &&  {}·I?·(({OI}·({!I})^*) + 
   ({O, I}) + {O, !I}·({!I})^*·{I})^* " @*/	


{

   do {
      yield;
      emit O();
   }every( I )
}

exports.prg = new hh.ReactiveMachine( prg, "everyimmediate" );
