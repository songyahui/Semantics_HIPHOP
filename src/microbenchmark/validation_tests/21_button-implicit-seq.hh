"use hopscript"

var hh = require( "hiphop" );

function plus( x, y ) { return x+y };

module BUTTON( in UL, in UR, in LL, in LR,
		      out WATCH_MODE_COMMAND,
		      out ENTER_SET_WATCH_MODE_COMMAND,
		      out SET_WATCH_COMMAND,
		      out NEXT_WATCH_TIME_POSITION_COMMAND,
		      out EXIT_SET_WATCH_MODE_COMMAND,
		      out TOGGLE_24H_MODE_COMMAND,
		      out TOGGLE_CHIME_COMMAND,
		      out STOPWATCH_MODE_COMMAND,
		      out START_STOP_COMMAND,
		      out LAP_COMMAND,
		      out ALARM_MODE_COMMAND,
		      out ENTER_SET_ALARM_MODE_COMMAND,
		      out SET_ALARM_COMMAND,
		      out NEXT_ALARM_TIME_POSITION_COMMAND,
		      out TOGGLE_ALARM_COMMAND,
		      out STOP_ALARM_BEEP_COMMAND,
		      out EXIT_SET_ALARM_MODE_COMMAND ) 
   /*@ requires "True && emp" @*/
   /*@ ensures "True && ({UR,  STOP_ALARM_BEEP_COMMAND} + {})^*" @*/					
{


   // global loop
   fork {
      loop {
		yield;
	 // watch / set-watch mode
	 emit WATCH_MODE_COMMAND();
	 
	 loop {
				yield;

	    // watch mode
	    abort( UL ) {
					yield;

	       fork {
		  emit LL();
	       } par {
		  loop {
					yield;

		     emit LR( );
		     emit TOGGLE_24H_MODE_COMMAND();
		  }
	       }
	    };
	    
	    // set watch-mode
	    emit ENTER_SET_WATCH_MODE_COMMAND();
	    abort( UL ) {
					yield;

	       fork {
		  loop {
					yield;

		     emit LL ();
		     emit NEXT_WATCH_TIME_POSITION_COMMAND();
		  }
	       } par {
		  loop {
					yield;

		     emit LR();
		     emit SET_WATCH_COMMAND();
		  }
	       }
	    };
	    emit EXIT_SET_WATCH_MODE_COMMAND();
	 };
	 
	 // stopwatch mode
	 emit STOPWATCH_MODE_COMMAND();
	 abort( LL ) {
				yield;

	    fork {
	       loop {
					yield;

		  emit LR (  );
		  emit START_STOP_COMMAND();
	       }
	    } par {
	       loop {
		  emit UR( );
		  emit LAP_COMMAND();
	       }
	    }
	 };
	 
	 // alarm / set alarm mode
	 emit ALARM_MODE_COMMAND();
	 loop {
				yield;

	    // alarm mode
	    abort( UL ) {
					yield;

	       fork {
		  fork {
		     emit LL (  );
		  } par {
		     loop {
						yield;

			emit LR( );
			emit TOGGLE_CHIME_COMMAND();
		     }
		  }
	       } par {
		  loop {
					yield;

		     emit UR( UR );
		     emit TOGGLE_ALARM_COMMAND();
		  }
	       }
	    };
	    
	    // set-alarm mode
	    emit ENTER_SET_ALARM_MODE_COMMAND();
	    abort( UL ) {
					yield;

	       fork {
		  loop {
					yield;

		     emit LL( LL );
		     emit NEXT_ALARM_TIME_POSITION_COMMAND();
		  }
	       } par {
		  loop {
					yield;

		     emit LR ( LR );
		     emit SET_ALARM_COMMAND();
		  }
	       }
	    };
	    emit EXIT_SET_ALARM_MODE_COMMAND();
	 }
      }
   } par {
     present (UR){
	 emit STOP_ALARM_BEEP_COMMAND();
      }
   }
}

exports.prg = new hh.ReactiveMachine( BUTTON, "BUTTON" );
