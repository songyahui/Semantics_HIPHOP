"use hopscript"

var hh = require( "hiphop" );

hiphop module prg( out A, in B, out END1, out END2 ) 

   /*@ requires "True && emp" @*/
   /*@ ensures "True && {A}.B?.{} // A?.{B}.{END2}" @*/	

{

   fork { // {A}.B?.{End1}
      emit A();
      await ( B );
      emit END1();
   } par { // A?.{B}.{End2}
      await ( A );
      emit B();
      yield;
      emit END2();
   }
}

exports.prg = new hh.ReactiveMachine( prg, "crossawait" );
