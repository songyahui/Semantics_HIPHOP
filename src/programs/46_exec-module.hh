"use hopscript"

hiphop module M1( a ) 
   /*@ requires emp    @*/
   /*@ ensures  {a}.({}^*||{B}.{a}) @*/
{
   emit a( 100 );
   async a {
      emit B; this.notify( 10 );
   }
}

hiphop module m( a, b ) 
 /*@ requires emp    @*/
/*@ ensures  ({a}.({}^*||{B}.{a})). ({a}.({}^*||{B}.{a})) @*/
{
   run M1( a  );
   yield;
   run M1( a );
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
