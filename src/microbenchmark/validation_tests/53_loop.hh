"use hiphop"
"use hopscript"

const hh = require( "hiphop" );

hiphop module a_loop( out A, out B, out C ) 

   /*@ requires "True && emp" @*/
   /*@ ensures "t>1 && {A,B}.({B, C}^*)" @*/	

{

  emit A ();
  loop {
  	   emit B(); 
     yield; 
     emit C()
  }

}

