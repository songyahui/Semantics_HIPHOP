hiphop module a_bug( out S ) 

   /*@ requires "True && {}" @*/
   /*@ ensures "True && {S}" @*/	

{

   signal S;
   present (S) {emit S ();}
   else {emit S ();}
}

