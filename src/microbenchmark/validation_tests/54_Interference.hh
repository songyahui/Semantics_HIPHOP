"use hiphop"
"use hopscript"

const hh = require( "hiphop" );

module a_loop(out J ) 

   /*@ requires "True && emp" @*/
   /*@ ensures "True && ({I, J})" @*/	
      /*@ ensures "True && ({I,!J})" @*/	


{
   signal I;
   fork{
      present( I ) {emit J()};
   }
   par{
      emit I();
   }

}

