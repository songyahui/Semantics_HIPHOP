"use hopscript"

var hh = require( "hiphop" );

module prg( in I, O ) 

   /*@ requires "True && emp" @*/
   /*@ ensures "True && ({}·{A, !S}·S?·{B, !S}) + ({}·{S, A}) + {}·{A, !S}·{S} " @*/	

{
   abort(S) {
      yield;
      emit A;
      await S;
            emit B;

   }

}

exports.prg = new hh.ReactiveMachine( prg, "everydelay" );

