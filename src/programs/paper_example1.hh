module main (out Prep, in Tick, out Ready, out Go, out Cook)

/*@ requires "True && emp" @*/
/*@ ensures  "(0<=t && t<3) && (({}.{Cook})#t).({}^*)" @*/
//  "(0<=t && t<3) && (({Prep}.{Cook})#t).{Ready}.{Go}"   @*/


{
	fork{ // One thread produces: true /\ Ready?.{Go}
		await Ready; 
		emit Go (); 
	} par{ // The other thread produces: 0<t<3 /\ {Prep, Cook}#t.{Ready}
		emit Prep ();
		async Ready { run cook (3, Tick, Cook); }
	}
}
      
module cook (var d, in Tick, out Cook)
  
/*@ requires "d>2  && {Prep}" @*/
/*@ ensures  "(0<=t && t<d) && ({}. {Cook})#t" @*/

{	
	abort count(d, Tick) { 
		yield; 
		emit Cook(); 
	}
}


