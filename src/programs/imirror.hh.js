"use hiphop";

const hh = require( "hiphop" );

hiphop interface Intf( in I, out O );

module M1() implements Intf {
   if( now( I ) ) emit O();
}

module M2( out OK ) implements mirror Intf {
   emit I();
   if( now( O ) ) emit OK();
}

module Main( OK ) {
   signal implements Intf;

   fork {
      run M1( ... );
   } par {
      run M2( OK, ... );
   }
}

const m = new hh.ReactiveMachine( Main );
m.addEventListener( "OK", v => console.log( "got OK" ) );

m.react();
