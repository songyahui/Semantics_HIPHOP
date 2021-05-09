hiphop module a_bug( out S ) 

   /*@ requires "True && {}" @*/
   /*@ ensures "True && {S}" @*/	

{

   signal S;
   if (S.now) {emit S ();}
   else {emit S ();}
}

