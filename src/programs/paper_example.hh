hiphop module authenticate (
		var d, 
	 	var name, 
	 	var passwd, 
	 	in Tick, 
	 	out Connecting, 
	 	out Connected)
	 
/*@ requires "d>3  && {Login} " @*/
/*@ ensures  "(d>3 && t<3 && t<d) && ({Connecting}.{Connected}) #t
		  \\/ t1=d && {Connecting}#t1 " @*/

{
	abort count(d, Tick) { // Abort the execution at d seconds
		async Connected {
			emit Connecting (); 
			// Execute authenticateSvc after a 3 seconds' delay
			setTimeout(
              	authenticateSvc(name, passwd).post().then( v => this.notify(v)), 3); }}}

