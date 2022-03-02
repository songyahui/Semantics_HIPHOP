"use hiphop"
"use hopscript"

const hh = require( "hiphop" );

hiphop module a_loop(out J ) 

   /*@ requires "True && emp" @*/
   /*@ ensures "True && {I, J}" @*/	

{
   signal I;
   fork{
      if( I.now ) {emit J()};
   }
   par{
      emit I();
   }

}

