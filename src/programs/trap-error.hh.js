"use hiphop";
"use hopscript"

var hh = require( "hiphop" );

module sub() {
   break T;
}

module main( O, S ) {
   T: {
      run sub();
   }
}

prg = new hh.ReactiveMachine( main, "abort-error" );
exports.prg = prg;


