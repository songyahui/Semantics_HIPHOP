"use hiphop"
"use hopscript"

var hh = require("hiphop");

module read ( in Open, in Close, out Loading, out Loaded, out CompOther, out LogData ) 
   /*@ requires "True && {}^* · {Open} "@*/
   /*@ ensures  "True && {CompOther, Loading}·{Loaded}·{LogData}· Close? " @*/
{
    async (Loaded) {
        emit Loading; 
    };
    emit CompOther;
    await( Loaded );
    emit LogData;
    await( Close );
}

module main (out Open, out Close, out Loading, out Loaded, out CompOther, out LogData ) 
   /*@ requires "True && {} "@*/
   /*@ ensures  "True && {Open}·  {}^* · {Close}" @*/
{
    emit Open;
    fork {
        read (Open, Close, Loading, Loaded, CompOther, LogData)
    }par {
        await (LogData);
        emit Close;
    }
}


exports.prg = new hh.ReactiveMachine( prg, "ABCRO" );


