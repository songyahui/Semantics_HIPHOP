hiphop module main (out Prep, in Tick, out Ready, out Go, out Cook)
/*@ requires true : emp @*/
/*@ ensures  0<=t/\t<3 : ({Prep}.{Cook})#t.{Ready}.{Go} @*/
{
	fork{ // One thread produces: true /\ Ready?.{Go}
		await Ready; emit Go (); 
	} par{ // The other thread produces: 0<t<3 /\ {Prep, Cook}#t.{Ready}
		emit Prep ();
		async Ready { run cook (3, Tick, Cook); }}}
      
hiphop module cook (var d, in Tick, out Cook)
/*@ requires d>2  : {Prep} @*/
/*@ ensures  0<=t/\t<d : {Cook}#t @*/
{	abort count(d, Tick) { yield; emit Cook(); }}


hiphop module authenticate (var d, var name, var passwd, in Tick, out Connecting, out Connected)
/*@ requires d>3 : {Login} @*/
/*@ ensures  (d>t/\t>3 : {Connecting}#t.{Connected}) \/ (t>=d : {Connecting}#t) @*/
{
	abort count(d, Tick) { // Abort the execution at d seconds
		async Connected {
			emit Connecting (); 
			// Execute authenticateSvc after a 3 seconds' delay
			setTimeout(authenticateSvc(name, passwd).post().then( v => this.notify(v)), 3); }}}