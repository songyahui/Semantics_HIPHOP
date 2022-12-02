
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
"use hopscript"

var hh = require( "hiphop" );

function foo( evt ) {
console.log( "foo called by", evt.type, "with value", evt.nowval );
}

function foo2( evt ) {
console.log( "foo2 called by", evt.type, "with value", evt.nowval );
}

function foo3( evt ) {
console.log( "foo3 called by", evt.type, "with value", evt.nowval );
}


module prg( in I, out O )
/*@ requires "True && emp" @*/
/*@ ensures "True && {}·(I?·{O})^*" @*/
/*@ ensures "True && {}·({O})^*" @*/

{

loop {
await( I );
emit O( );
}
}

var m = new hh.ReactiveMachine( prg, "awaitvalued2" );
m.debug_emitted_func = console.log;

m.addEventListener( "O", foo );

console.log( ";" );
m.react();

m.addEventListener( "O", foo2 );

console.log( "I(34)" );
m.inputAndReact( "I", 34 );

m.addEventListener( "O", foo3 );

console.log( "I(34)" );
m.inputAndReact( "I", 34 );

m.removeEventListener( "O", foo3 );

console.log( "I(15)" );
m.inputAndReact( "I", 15 );
"use hopscript"

var hh = require( "hiphop" );

module prg( out A, in B, out END1, out END2 )

/*@ requires "True && emp" @*/
/*@ ensures "True && {A}·(B?·{END1} // A?·{B}·{END2})" @*/
/*@ ensures "True && {A}·(B?·{END1} . A?·{B}·{END2})" @*/


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
"use hiphop"
"use hopscript"

const hh = require( "hiphop" );

module prg( in X, out Y, out Z )

/*@ requires "True && emp" @*/
/*@ ensures "True && {}·X?·Z?·(({Y, !Z}·({!Z})^*) + ({Y, Z}) + {Y, !Z}·({!Z})^*·{Z})^*" @*/
/*@ ensures "True && {}·X?·Z?·(({Y, !Z}·({!Z})) + ({Y, Z}) + {Y, !Z}·({!Z})^*·{Z})^*" @*/

{

await( X );


do {
yield;
emit Y();
} every (Z);


}

var m = new hh.ReactiveMachine( prg );

"use hopscript"

var hh = require( "hiphop" );

module example( out I, out O )

/*@ requires "True && emp" @*/
/*@ ensures "True && {}·(({O, I}·{O}) + {!O}·{O})^*" @*/
/*@ ensures "True && {}·(({O, I}·{O}) + {!O}·{!O})^*" @*/

{

loop {
yield;
present( O ) {emit I()};
yield;
emit O();
}
}

exports.prg = new hh.ReactiveMachine( example, "presentemit" );
"use hopscript"

var hh = require( "hiphop" );

module example( out I, in O )

/*@ requires "True && emp" @*/
/*@ ensures "True && {}·(({now(O), I, O}·{}) + {!now(O), O}·{})^*" @*/
/*@ ensures "True && {}·(({now(O), I, O}·{}) + {now(O), O}·{})^*" @*/


{

loop {
yield;
present( now( O ) ) {emit I()};
emit O();
yield;
}
}

exports.prg = new hh.ReactiveMachine( example, "presentemit" );
"use hopscript"

const hh = require( "hiphop" );

module prg()

/*@ requires "True && emp" @*/
/*@ ensures "True && {}" @*/
/*@ ensures "True && emp" @*/


{
// currently trap has not fully implemented.
trap {
trap {
exit 2;
};
hop { console.log( "first level" ) };
};
hop { console.log( "top level" ) };
}

var m = new hh.ReactiveMachine( prg );

m.react();
"use hopscript"

const hh = require( "hiphop" );

module prg( out A, in B )

/*@ requires "True && emp" @*/
/*@ ensures "True &&  {}·(({B, A}·{}) + {!B}·{})^* " @*/
/*@ ensures "True &&  {}·(({B, A}) + {!B}·{})^* " @*/


{

loop {
yield;
present( B ) {emit A()};
yield;
}
}

const m = new hh.ReactiveMachine( prg );
m.debug_emitted_func = console.log;

m.react();
m.react();
m.inputAndReact( "B" );
m.react();
m.inputAndReact( "B" );
m.inputAndReact( "B" );

"use hopscript"

const hh = require( "hiphop" );

module prg( out A, out B, out C )

/*@ requires "True && emp" @*/
/*@ ensures "True && ({}·{A, B, B(4), C}·{}·{A, B, B(4), C}·{}·{A, B, B(4), C}·{}) + ({}·{A, B, B(4), C}·{}·{A, B, B(4), C}·{}·{A, B, B(3), !C}) + ({}·{A, B, B(4), C}·{}·{A, B, B(4), C}·{}·{B(4), C, !B}) + ({}·{A, B, B(4), C}·{}·{A, B, B(4), C}·{}·{B(3), !B, !C}) + ({}·{A, B, B(4), C}·{}·{A, B, B(3), !C}) + ({}·{A, B, B(4), C}·{}·{B(4), C, !B}) + ({}·{A, B, B(4), C}·{}·{B(3), !B, !C}) + ({}·{A, B, B(3), !C}) + ({}·{B(4), C, !B}) + {}·{B(3), !B, !C} " @*/
/*@ ensures "True && ({}·{A, B, B(4), C}·{}·{A, B, B(4), C}·{}·{A, B, B(4), C}·{}) + ({}·{A, B, B(4), C}·{}·{A, B, B(4), C}·{}·{A, B, B(3), !C}) + ({}·{A, B, B(4), C}·{}·{A, B, B(4), C}·{}·{B(4), C, !B}) + ({}·{A, B, B(4), C}·{}·{A, B, B(4), C}·{}·{B(3), !B, !C}) + ({}·{A, B, B(4), C}·{}·{A, B, B(3), !C}) + ({}·{A, B, B(4), C}·{}·{B(3), !B, !C}) + ({}·{A, B, B(3), !C}) + ({}·{B(4), C, !B}) + {}·{B(3), !B, !C} " @*/

{

fork {
loop {
yield;
present( B) {emit A()};
yield;
}
} par {
loop {
yield;
present( C ) {
emit B( 4 );
} else {
emit B( 3 );
} ;
yield;
}
}
}

const m = new hh.ReactiveMachine( prg );
m.debug_emitted_func = console.log;

m.react();
m.react();
m.inputAndReact( "C" );
m.react();
m.inputAndReact( "C" );
m.inputAndReact( "C" );

"use hopscropt"

const hh = require( "hiphop" );

module prg( out A, out B )

/*@ requires "True && emp" @*/
/*@ ensures "True && {A, B} " @*/
/*@ ensures "True && ({A, B})^* " @*/


{

emit A();
emit B();
}

const m = new hh.ReactiveMachine( prg );
m.debug_emitted_func = console.log;

m.react();
m.react();
"use hopscript"

const hh = require( "hiphop" );

module prg( out O )

/*@ requires "True && emp" @*/
/*@ ensures "True &&  {}·({O(5)}·{})^* " @*/
/*@ ensures "True &&  {}·({O(5)}·{})" @*/


{

loop {
yield;
emit O( 5 );
emit O( 5 );
yield;
}
}

const machine = new hh.ReactiveMachine( prg, "emiterror" );

"use hopscript"

var hh = require( "hiphop" );

module prg( out O )

/*@ requires "True && emp" @*/
/*@ ensures "True && {}·({O(5)}·{O})^* " @*/
/*@ ensures "True && {}·({O(4)}·{O})^* " @*/

{

loop {
yield;
emit O( 5 );
yield;
emit O();
}
}

exports.prg = new hh.ReactiveMachine( prg, "emitnovalue" );
"use hopscript"

var hh = require( "hiphop" );

module prg( out O )

/*@ requires "True && emp" @*/
/*@ ensures "True && {}·({S, O}·{O}·{})^*" @*/
/*@ ensures "True && {}·({S, O}·{O}·{})" @*/


{

loop {
yield;
signal S ;//= 1;

emit S(   );
emit O(  );
yield;
emit O(  );
yield;
}
}

exports.prg = new hh.ReactiveMachine( prg, "emitvaluedlocal1" );
"use hopscript"

var hh = require( "hiphop" );

function sum( arg1, arg2 ) {
return arg1 + arg2;
};

module prg( out O )

/*@ requires "True && emp" @*/
/*@ ensures "True && {}·({S, O})^*" @*/

/*@ ensures "True && ({S, O})^*" @*/

{

loop {
yield;
signal S ;//= 1;

emit S( );
emit O(  );


}
}

exports.prg = new hh.ReactiveMachine( prg, "emitvaluedlocal2" );
"use hopscript"

var hh = require( "hiphop" );

module prg( in I, O )

/*@ requires "True && emp" @*/
/*@ ensures "True && ({}·{A, !S}·S?·{B, !S}) + ({}·{S, A}) + {}·{A, !S}·{S} " @*/
/*@ ensures "True && ({}·{A, !S}·S?·{B, !S}) + ({}·{S, A}) + {}·{AS}·{S} " @*/

{
abort(S) {
yield;
emit A;
await S;
emit B;

}

}

exports.prg = new hh.ReactiveMachine( prg, "everydelay" );

"use hopscript"

var hh = require( "hiphop" );

module prg( in I, O )

/*@ requires "True && emp" @*/
/*@ ensures "True &&  {}·I?·(({O, !I}·({!I})^*) +
({O, I}) + {O, !I}·({!I})^*·{I})^* " @*/

/*@ ensures "True &&  {}·I?·(({OI}·({!I})^*) +
({O, I}) + {O, !I}·({!I})^*·{I})^* " @*/


{

do {
yield;
emit O();
}every( I )
}

exports.prg = new hh.ReactiveMachine( prg, "everyimmediate" );
"use hiphop";
"use hopscript";

const hh = require( "hiphop" );

module prg( in I, out O )

/*@ requires "True && emp" @*/
/*@ ensures "True && I?.{O}. (I?.{O})^* " @*/
/*@ ensures "True && I?.{O}. (I?.{O}) " @*/


{

do {
yield;
emit O();

}every( I )
}

exports.prg = new hh.ReactiveMachine( prg, "every1" );
"use hopscript"

var hh = require( "hiphop" );

module prg( in I, out S )

/*@ requires "True && emp" @*/
/*@ ensures "True && {}·(I?·{S})^*" @*/
/*@ ensures "True && {}·I?·{S}.(I?·{S})^*" @*/


{

loop {
await( I );
yield;
emit S();
}
}

exports.prg = new hh.ReactiveMachine( prg, "looppauseemit" );
"use hiphop";
"use hopscript";

var hh = require( "hiphop" );

module prg( J )

/*@ requires "True && emp" @*/
/*@ ensures "True && {I}·I?·{J} " @*/
/*@ ensures "True && I?·{J} " @*/


{

signal I;

fork {
emit I();
} par {
await( I );
emit J();
}
}

exports.prg = new hh.ReactiveMachine( prg, "parallel" );
"use hopscript"

var hh = require( "hiphop" );

module prg( out J )

/*@ requires "True && emp" @*/
/*@ ensures "True && ({I, J} ) " @*/

/*@ ensures "True && ({I, J}.{} ) " @*/


{

signal I;

fork {
present ( I ) {emit J()};
} par {
emit I();
}
}

exports.prg = new hh.ReactiveMachine( prg, "parallel2" );
"use hiphop";
"use strict";

var hh = require( "hiphop" );

module prg( out T )

/*@ requires "True && emp" @*/
/*@ ensures "True && {S}  " @*/
/*@ ensures "True && {!S}  " @*/


{



signal S;

emit S();

present( S ) {emit T()};

}

exports.prg = new hh.ReactiveMachine( prg, "example1" );
"use hopscript"

var hh = require( "hiphop" );

module prg( T, V )

/*@ requires "True && emp" @*/
/*@ ensures "True && {}·({S, T}·{V})^* " @*/
/*@ ensures "True && {}·({ST}·{V})^* " @*/


{

signal S;

loop {
yield;
emit S();
present( S ) {emit T()};
yield;
emit V();
}
}

exports.prg = new hh.ReactiveMachine( prg, "example2" );
"use hopscript"

var hh = require( "hiphop" );

module prg( in A, T, V )

/*@ requires "True && emp" @*/
/*@ ensures "True && ({}·({S, T, !A}·{V, !A})^*) + ({}·({S, T, !A}·{V, !A})^*·{S, T, A}) + {}·({S, T, !A}·{V, !A})^*·{S, T, !A}·{V, A} " @*/
/*@ ensures "True && ({}·({S, T, !A}·{V, !A})^*) + ({}·({S, T, !A}·{V, !A})^*·{S, T, A}) + {}·({S, T, !A}·{V, !A})^*·{S, T, !A}·{VA} " @*/

{

abort( A ) {
signal S;

loop {
yield;

emit S();

present( S ) {emit T()};

yield;
emit V();
}
}
}

exports.prg = new hh.ReactiveMachine( prg, "example3" );
"use hopscript"

var hh = require( "hiphop" );

module prg( in A, out T, out V )

/*@ requires "True && emp" @*/
/*@ ensures "True && {}·(({}·{S, T, !A}·{V, !A}) + ({}·{S, T, A}) + {}·{S, T, !A}·{V, A})^* " @*/
/*@ ensures "True && {}·(({}·{S, T, !A}·{V, !A}) + ({}·{S, T, A}) + {}·{S, T, !A}·{V, A}) " @*/


{


signal S;

loop {
yield;
abort( A ) {
yield;
emit S();
present( S ) {emit T()} else{};
yield;
emit V();
}
}
}

exports.prg = new hh.ReactiveMachine( prg, "example4" );
"use hopscript"

module M1( in A )

/*@ requires "True && {}^*" @*/
/*@ ensures "True && {A(100)}·{A}  " @*/
/*@ ensures "True && {A(50)}·{A}  " @*/


{

emit A( 100 );
async (A) {
this.notify( 10 );
};
}

module m( a, b )
/*@ requires "True && emp" @*/
/*@ ensures "True && {}·{A(100)}·{A}  " @*/
/*@ ensures "True && {}·{A(50)}·{A}  " @*/


{
M1( a);
}

m.addEventListener( "a", e => console.log( "a=", e.nowval ) );
m.addEventListener( "b", e => console.log( "b=", e.nowval ) );

m.react();
m.react();
"use hopscript"

module M1( in A , out B)

/*@ requires "True && {}^*" @*/
/*@ ensures "True && {A(100), B}·{A}  " @*/
/*@ ensures "True && {A(100)}·{!A}  " @*/
{
emit A( 100 );
async A {
emit B (); this.notify( 10 );
};
}

module m( a, b )

/*@ requires "True && emp" @*/
/*@ ensures "True && {}.{A(100), B}·{A}.{}  " @*/
/*@ ensures "True && {}.{A(100), B}·{A}  " @*/


{
M1( a  );
yield;
// run M1( a ); // adding this line will couse failure on precondition check.
}



m.addEventListener( "a", e => console.log( "a=", e.nowval ) );
m.addEventListener( "b", e => console.log( "b=", e.nowval ) );

m.react();
m.react();
m.react();
m.react();
m.react();
m.react();
m.react();
m.react();


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
