"use hiphop"
"use hopscript"

const hh = require( "hiphop" );

hiphop module prg( in I, J, K ) {
   loop {
      abort( I.now ) {
	 sustain J();
      }
      emit K();
      {K(1)}. {K(2)}
       
   }
}

exports.prg = new hh.ReactiveMachine( prg, "sustain1" );
