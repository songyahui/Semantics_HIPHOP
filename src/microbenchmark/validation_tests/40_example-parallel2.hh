"use hopscript"

var hh = require( "hiphop" );

module prg( out J ) 

   /*@ requires "True && emp" @*/
   /*@ ensures "True && ({I, J} ) " @*/	

      /*@ ensures "True && ({I, J}.{} ) " @*/	


{

   signal I;
   
   fork {
      present ( I ) {emit J()};
   } par {
      emit I();
   }
}

exports.prg = new hh.ReactiveMachine( prg, "parallel2" );
