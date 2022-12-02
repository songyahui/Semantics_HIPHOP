
"use hiphop"
"use hopscript"

var hh = require("hiphop");

module prg( in A, in B, in C, in R, out O )
/*@ requires "True && emp "@*/
/*@ ensures  "True && {} . (A? // B? // C?).{R}" @*/
/*@ ensures  "True && {} . (A? // B? // C?)" @*/

{
fork {
await( A );
} par {
await( B );
} par {
await( C );
};
yield;
emit R;

}
exports.prg = new hh.ReactiveMachine( prg, "ABCRO" );
"use hiphop"
"use hopscript"

var hh = require( "hiphop" );


module prg( in I, out O )
/*@ requires "True && emp" @*/
/*@ ensures "True && ({}·{O, !L}·{L, O}·{}) + {}·{L, O}·{}" @*/
/*@ ensures "True && ({}·{O, !L}·{L, O}) + {}" @*/

{
signal L;

fork {
abort( L ) {
loop {
yield;
emit O;

}
}
} par {
await( O );
emit L;
};
yield;
}

exports.prg = new hh.ReactiveMachine( prg, "abortpar" );

// ({}·({O, !L})^*) + {}·({O, !L})^*·{O, L}
"use hiphop"
"use hopscript"

const hh = require("hiphop");

module prg(out A, out B, out C )
/*@ requires "True && emp" @*/
/*@ ensures "True && {A(0), B(1), C(2)}·{}·{}" @*/
/*@ ensures "True && {A(0), B(1), C(2)}" @*/

{

fork {
// loop {
emit A( 0 );
yield;
//  }
} par {
//  loop {
emit B( 1 );
yield;
//  }
} par {
//  loop {
emit C( 2 );
yield;
//  }
};
yield;
}

let machine = new hh.ReactiveMachine( prg, "error2" );
"use hiphop"
"use hopscript"

var hh = require("hiphop");

module prg( in A, in B, in C, in R, out O )
/*@ requires "True && emp "@*/
/*@ ensures  "True && {}·R?·
(({A, !R}·({!R})^*) + ({A, R}) + {A, !R}·({!R})^*·{R})^*" @*/
/*@ ensures  "True &&
(({A, !R}·({!R})^*) + ({A, R}) + {A, !R}·({!R})^*·{R})^*" @*/

{
do {
yield;
emit A ;


} every( R )
}
exports.prg = new hh.ReactiveMachine( prg, "ABCRO" );
"use hiphop"
"use hopscript"

var hh = require( "hiphop" );

module prg( in I, out O )
/*@ requires "True && emp" @*/
/*@ ensures "True && ({}·({O, !L})^*) + {}·({O, !L})^*·{O, L}" @*/
/*@ ensures "True && (({O, !L})^*) + {}·({O, !L})^*·{O, L}" @*/

{
signal L;
abort( L ) {
loop {
yield;
emit O;

}
}


}

exports.prg = new hh.ReactiveMachine( prg, "abortpar" );
"use hopscript"

var hh = require( "hiphop" );

module prg
( in I, out J,
out K, out V )

/*@ requires "True && emp" @*/
/*@ ensures "True && ({}·{J, !I}·{V, !I}) + ({}·{J, I, K}) + {}·{J, !I}·{V, I, K}" @*/
/*@ ensures "True && ({}·{J, !I}·{V, !I}) + {}·{J, !I}·{V, I, K}" @*/

{

abort( I ) {
yield;
emit J;
yield;
emit V;
};
present( I ) {
emit K;
}
}

exports.prg = new hh.ReactiveMachine( prg, "abortpresent" );
"use hiphop"
"use hopscript"

var hh = require( "hiphop" );

module prg(out O, out S )
/*@ requires "True && emp" @*/
/*@ ensures "True && {}·(({A, !S}·{O, !S}) + ({A, S}) + {A, !S}·{O, S})^*" @*/
/*@ ensures "True && {}·(({A, !S}·{O, !S}) + ({A, S}) + {A, !S}·{O, S})" @*/


{
loop {
abort( S ) {
yield;
emit A;
yield;
emit O;
};
}
}


exports.prg = new hh.ReactiveMachine(prg, "abortpre");
"use hopscript"

var hh = require("hiphop");

module prg( in A, in B, in R, out O )
/*@ requires "True && emp" @*/
/*@ ensures "True && {}·(({A, !S}·{O, !S, I, K}) + ({A, !S}·{O, !S, !I}) + ({A, S, I, K}) + ({A, S, !I}) + ({A, !S}·{O, S, I, K}) + {A, !S}·{O, S, !I})^*" @*/
/*@ ensures "True && {}·(({A, !S}·{O, !S, I, K}) + ({A, !S}·{O, !S, !I}) + ({A, S, I, K}) + ({A, S, !I}) + ({A, !S}·{O, S, I, K}) + {A, !S}·{O, S, !I})" @*/

{

loop {
abort( S ) {
yield;
emit A;
yield;
emit O;
};
present( I ) {
emit K;
}
}
}

exports.prg = new hh.ReactiveMachine( prg, "ABRO" );


"use hiphop"
"use hopscript"

const hh = require( "hiphop" );

module prg( in A, in B, in R, out O )
/*@ requires "True && emp" @*/
/*@ ensures "True && {}·(A? // B?)·{O}" @*/
/*@ ensures "True && {}·(A? . B?)·{O}" @*/

{


fork {
await( A );
} par {
await( B );
};
emit O;

}

exports.prg = new hh.ReactiveMachine( prg, "ABRO" );
"use strict"

var hh = require("hiphop");

module prg()
/*@ requires "True && emp" @*/
/*@ ensures "True && {}·({L()}·{})^*" @*/
/*@ ensures "True && {}·({L()}·{})" @*/

{

loop {
yield;
signal L;

emit L();
yield;
hop { console.log( "atom works! value of L is", L.nowval ) }
}
}

exports.prg = new hh.ReactiveMachine(prg, "atom");
"use strict"

var hh = require( "hiphop" );

function func() {
console.log( "atom works!" );
}

module prg(out A, out B)
/*@ requires "True && emp" @*/
/*@ ensures "True && {}·({A}·{B})^*" @*/
/*@ ensures "True && {}·({A}·{B})" @*/

{
loop {
yield;
emit A ();
yield;
emit B ();
hop { func() };
}
}

exports.prg = new hh.ReactiveMachine( prg, "atom" );
module Authenticate(
in name,
in passwd,
out connState,
out connected)

/*@ requires "True && emp" @*/
/*@ ensures "True && {connState}·{connected}" @*/
/*@ ensures "True && {connState}·{!connected}" @*/

{

emit connState();
async connected {
() //authenticateSvc(name.nowval, passwd.nowval).post().then(v => this.notify(v));
};
}
"use hopscript"

var hh = require( "hiphop" );

module prg( in I, out O )
/*@ requires "True && emp" @*/
/*@ ensures "True && {}·(I?·I?·I?·{O})^*" @*/
/*@ ensures "True && {}·(I?·I?·{O})^*" @*/


{

loop {
await I;
await I;
await I;

emit O;
}
}

exports.prg = new hh.ReactiveMachine( prg, "await3" );
"use hiphop"
"use hopscript"

const hh = require( "hiphop" );

module prg( in Tick, out O )
/*@ requires "True && emp" @*/
/*@ ensures "True && {}·(Tick?·Tick?·Tick?·{O})^*" @*/
/*@ ensures "True && {}·(Tick?·Tick?·Tick?·{O})" @*/

{

loop {
await Tick;
await Tick;
await Tick;

emit O();
}
}

exports.prg = new hh.ReactiveMachine( prg, "await3" );
"use hiphop"
"use hopscript"

var hh = require( "hiphop" );

module prg( in I, out O )
/*@ requires "True && emp" @*/
/*@ ensures "True && {}·(I?·I?·I?·{O})^*" @*/
/*@ ensures "True && {}·(I?·I?·I?·{O})" @*/

{

loop {
await I;
await I;
await I;
emit O();
}
}

exports.prg = new hh.ReactiveMachine( prg, "await3" );
"use hopscript"

var hh = require( "hiphop" );

module prg( in I, out O )
/*@ requires "True && emp" @*/
/*@ ensures "True && {}·(I?·{O}·{})^*" @*/
/*@ ensures "True && {}·(I?·{O})^*" @*/


{
loop {
await ( I );
emit O;
yield;
}
}

exports.prg = new hh.ReactiveMachine( prg, "awaitimmediate" );
"use hiphop"
"use hopscript"


var hh = require( "hiphop" );

module prg( in A, in B, out O )
/*@ requires "True && emp" @*/
/*@ ensures "True &&  {}·(A? // B?)·{O}" @*/
/*@ ensures "True &&  {}·(A? // B?)" @*/

{

fork {
await( A );
} par {
await( B );
};
emit O;
}

exports.prg = new hh.ReactiveMachine( prg, "awaitpar" );
"use hopscript"

var hh = require( "hiphop" );

module prg( in A, in B, out O )
/*@ requires "True && emp" @*/
/*@ ensures "True && {}·A?·B?·{O}" @*/
/*@ ensures "True && B?·{O}" @*/

{

await( A );
await( B );
emit O;
}

exports.prg = new hh.ReactiveMachine( prg, "awaitseq" );
"use hiphop"
"use hopscript"

var hh = require( "hiphop" );

module prg( in A, in B, out O )
/*@ requires "True && emp" @*/
/*@ ensures "True && {}·A?·B?·{O}" @*/
/*@ ensures "True && {}·A?·B?" @*/


{
await( A );
await( B );
emit O;
}

exports.prg = new hh.ReactiveMachine( prg, "awaitseq" );
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
