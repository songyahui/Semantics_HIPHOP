"use hiphop"
"use hopscript"

var hh = require( "hiphop" );

function foo( evt ) {
   console.log( "foo called by", evt.type, "with value", evt.nowval );
};

module prg( in I, out O ) 
   /*@ requires "True && emp" @*/
   /*@ ensures "True && {}·I?·{O}" @*/
      /*@ ensures "True && {}·I?·{O}.{}·I?·{O}" @*/


{

   await( I );
   emit O( );
}

var m = new hh.ReactiveMachine( prg, "awaitvalued" );
m.addEventListener( "O", foo );

exports.prg = m;
