"use hiphop"
"use hopscript"

const hh = require( "hiphop" );

module a_loop( out A, out B, out C ) 

   /*@ requires "True && emp" @*/
   /*@ ensures "True && {A}·({B}·{C})^*" @*/	
      /*@ ensures "True && {A}·({B}·{C})" @*/	


{

  emit A ();
  loop {
   yield; 
  	   emit B(); 
     yield; 
     emit C()
  }

}

