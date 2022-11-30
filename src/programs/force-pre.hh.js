"use hiphop"
"use hopscript"

var hh = require( "hiphop" );

try {
   module prg( O=0 ) {
      emit O( O.nowval );
   }
} catch( e ) {
   console.log( "error: self update" );
}
