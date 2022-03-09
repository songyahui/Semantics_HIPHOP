let tests =
  [
    (* Single Instant *)
    "True && {A}  |-  True && {A} : true";
    "True && {}   |-  True && {A} : false";
    "True && {A}  |-  True && {}  : true";
    (* Empty, Bottoms *)
    "True && emp  |-  True && {}  : false";
    "True && emp  |-  True && {A} : false";
    "True && emp  |-  True && emp : true";
    "True && _|_  |-  True && emp  : true";
    "True && _|_  |-  True && {}  : true";
    "True && _|_  |-  True && _|_ : true";
    "True && {}   |-  True && {}  : true";
    "True && {}   |-  True && _|_ : false";
    "True && {} .  _|_  |-  True && _|_ : true";
    "True && {} +  _|_  |-  True && _|_ : false";
    "True && {} // _|_  |-  True && _|_ : true";
    "True && {} // _|_  |-  True && _|_ : true";
    "True && _|_^*  |-  True && emp : true";
    "True && _|_^*  |-  True && _|_ : false";
    (* False pi *)
    "True && {}    |-  False && {}  : false";
    "False && {}   |-  True && {}   : true";
    "False && {}   |-  False && {}  : true";
    "False && {}   |-  False && _|_ : true";
    "False && emp  |-  False && _|_ : true";
    (* Sequence *)
    "True && {A}.{B}  |-  True && {A}.{B} : true";
    "True && {A}  |-  True && {A}.{B} : false";
    "True && {A}.{B}  |-  True && {B} : false";
    "True && {A}.{B}  |-  True && {}.{B} : true";
    "True && {A}.{B}  |-  True && {}.{}  : true";
    "True && {A}.{B}.{A}.{C}.{A, B}  |-  True && {}.{}.{}.{}.{}    : true";
    "True && {A}.{B}.{A}.{C}.{A, B}  |-  True && {A}.{}.{}.{C}.{A} : true";
    "True && {A}.{B}.{A}.{C}.{B}  |-  True && {A}.{}.{}.{C}.{A}    : false";
    "True && {A}.{B}.{A}.{C}.{B}  |-  True && {A}.{}.{}.{C}.{A}    : false";
    (* Union *)
    "True && {A} + {B}  |-  True && {A} : false";
    "True && {A}  |-  True && {A} + {B} : true";
    "True && {A} + {B}  |-  True && {B} + {A} : true";
    "True && ({A} + {C}) + {B}  |-  True && ({C} + {A}) + {B} : true";
    "True && {A} + ({C} + {B})  |-  True && {B} + ({A} + {C}) : true";
    "True && {A} + {B} + {C} + {D} + {E}  |-  True && {A, B, C, D, E} : false";
    "True && {A, B, C, D, E}  |-  True && {A} + {B} + {C} + {D} + {E} : true";
    (* Parallel *)
    "True && {A} // {B}  |-  True && {A} // {B} : true";
    "True && {A, B}  |-  True && {A} // {B} : true";
    "True && {A} // {B}  |-  True && {A, B} : true";
    "True && {A} // {B} // {C} // {D} // {E}  |-  True && {A, B, C, D, E} : true";
    "True && {A, B, C, D, E}  |-  True && {A} // {B} // {C} // {D} // {E} : true";
    (* Sequence, Union *)
    "True && {A}.{B} + {C}.{D}  |-  True && {C}.{D} + {A}.{B} : true";
    "True && {A}.({B} + {C}).{D}  |-  True && {}.{}.{} : true";
    "True && {A}.{B}.{C} + {C}.{B}.{A}  |-  True && {A}.{B}.{A} : false";
    "True && {A}.{B}.{C} + {C}.{B}.{A}  |-  True && {}.{B}.{}   : true";
    "True && {A, C}.{B}.{C} + {A, C}.{B}.{A}  |-  True && {A}.{B}.{} : true";
    "True && {A, C}.{B}.{C} + {A, C}.{B}.{A}  |-  True && {C}.{B}.{} : true";
    "True && {A}.{B}.{A}  |-  True && {A}.{B}.{C} + {C}.{B}.{A}       : false";
    "True && {A, C}.{B}.{A, C}  |-  True && {A}.{B}.{C} + {C}.{B}.{A} : true";
    (* Sequence, Parallel *)
    "True && {A}.{B} // {C}.{D}  |-  True && {C}.{D} // {A}.{B} : true";
    "True && {A}.({B} // {C}).{D}  |-  True && {}.{}.{} : true";
    "True && {A}.({B} // {C}).{D}  |-  True && {}.{B, C}.{} : true";
    "True && {A}.({B} // {C}).{D}  |-  True && {A}.{B, C}.{D} : true";
    "True && {A}.({B} // {C}).{D}  |-  True && {A}.{B}.{D} // {A}.{C}.{D} : true";
    "True && {A}.({B} // {C}).{D}  |-  True && ({A}.{B} // {A}.{C}).{D} : true";
    "True && {A}.{C}.{E} // {B}.{D}.{F}  |-  True && {A, B}.{C, D}.{E, F} : true";
    "True && {A}.{C}.{E} // {B}.{D}  |-  True && {A, B}.{C, D}.{E} : true";
    "True && {A}.{C}.{E} // {B, D}  |-  True && {B, D}.{C}.{E} : true";
    (* Kleene *)
    "True && {A}^*  |-  True && {A}^* : true";
    "True && {A}    |-  True && {A}^* : true";
    "True && {A}^*  |-  True && {A}   : false";
    "True && {A, B}^*   |-  True && {A}^* : true";
    "True && {A, B}^*   |-  True && emp^* : false";
    "True && {A, B}^*   |-  True && _|_^* : false";
    "False && {A, B}^*  |-  True && _|_^* : true";
    (* Kleene, Union, Parallel *)
    "True && ({A} + {B})^*  |-  True && {A}^* : false";
    "True && {A}^*  |-  True && ({A} + {B})^* : true";
    "True && ({A} + {B})^*  |-  True && ({B} + {A})^* : true";
    "True && ({A} + ({B} + {C}))^*  |-  True && ({B} + ({A} + {C}))^* : true";
    "True && ({A} + ({B} // {C}))^*  |-  True && {}^* : true";
    "True && ({A} + ({A} // {C}))^*  |-  True && {A}^* + ({A} + {C})^* : true";
    (* Sequence, Kleene *)
    "True && {A}.{B}^*.{C}.{A, B}  |-  True && {A}.{B}^*.{C}.{A}   : true";
    "True && {A}.{B}^*.{C}.{A, B}  |-  True && {A}.{B}^*.{}.{A}^*  : true";
    "True && {A}.{B}^*.{C}^*  |-  True && {A}^*.{B}^*.{C}^* : true";
    "True && {A}.{B}^*.{C}^*  |-  True && {A}^*.{B, C}^*    : false";
    "True && {A}.{B, C}^*  |-  True && {A}^*.{B}^*.{C}^*    : true";
    "True && {A}^*.{B}  |-  True && {A}^*.{C}  : false";
    "True && {A}^*.{B}  |-  True && {A}^*.{}   : true";
    (* Mixed *)
    "True && {A}.{B}^*.{C}^*    |-  True && {A}^*.({B} + {C})^*   : true";
    "True && {A}^*.{B}^*.{C}^*  |-  True && ({A} + {B} + {C})^*  : true";
    "True && ({A}.{B}.{C})^*    |-  True && ({A} + {B} + {C})^*  : true";
    "True && {B}.({A} + ({B} + {C}))^*  |-  True && ({B} + ({A} + {C}))^* : true";
    "True && {A, B}.({A} + ({B} // {C}))^*  |-  True && {}^* : true";
    "True && {A, C}.({A} + ({A} // {C}))^*  |-  True && {A}^* + ({A} + {C})^* : true";
    "True && {A, C}^*.({A} + ({A} // {C}))^*  |-  True && {A}^* + ({A} + {C})^* : true";
    "True && ({A}+{D}).{B, E}.({C}//{F})  |-  True && (({A}+{D}).{B, E}.({C}//{F}))^* : true";
    "True && (({A}+{D}).{B, E}.({C}//{F}))^*  |-  True && (({A}+{D}).{B, E}.({C}//{F}))^* : true";
    "True && (({A}+{D}).{B, E}.({C}//{F}))^*  |-  True && ({A}+{B}+{C}+{D}+{E})^* : true";
    (* Alternative Syntax *)
    {| True /\ {A, B}.{A, B}^*  |-  True /\ {A, B}^* : true |};
    {| True /\ ({A}.{B})^*      |-  True /\ {A, B}^* : false |};
    {| True /\ ({A}.{B})^*      |-  True /\ ({A} + {B})^* : true |};
    {| True /\ ({A}.{B})^*      |-  True /\ emp + {A}.{B}.({A} + {B})^* : true |};
    {| True /\ ({A}.{B})^*      |-  True /\ bot + {A}.{B}.({A} + {B})^* : false |};
    {| True /\ ({A}.{B})^* // {C}    |-  True /\ {A, C}.{B}.({A}.{B})^* : true   |};
    {| True /\ ({A}.{B})^* // {C}^*  |-  True /\ ({A, C}.{B, C})^* : true   |};
    {| True /\ ({A}.{B})^* // ({C} // {D})^*  |-  True /\ ({A, C}.{B, C})^* : true   |};
    {| True /\ {A, B} |-  True /\ {A} // {B} // {C} : false   |};
    (* Await *)
    "True && {A} // B?  |-  True && {A} : false";
    "True && A? // {B}  |-  True && {A} : false";
    "True && A? // {A}  |-  True && {A} : true";
    "True && {A}  |-  True && A? : true";
    "True && A?   |-  True && {}^*.{A} : true";
    "True && {A}  |-  True && A?       : true";
    "True && {A}  |-  True && {} // A? : true";
    "True && {}^*.{A}  |-  True && A?        : false";
    "True && A?        |-  True && {}^*.{A}  : true";
    "True && A?        |-  True && {A}^*.{A} : false";
    "True && {A} + {}.{A}  |-  True && A?   : false";
    "True && {B} // {A}  |-  True && A? // {B} : true";
    "True && {B} // {}.{A}  |-  True && A? // {B} : true";
    "True && {B} // {}.{}.{A}  |-  True && A? // {B} : true";
    "True && {B} // {}.{}.{}.{A}  |-  True && A? // {B} : true";
    "True && A?  |-  True && {B}.A? : false";
    "True && {B}.A?  |-  True && A? : true";
    "True && {B}.{B}.A?  |-  True && A? : true";
    "True && {B}.{B}.{B}.A?  |-  True && A? : true";
    "True && {A} // {}^*.{A}  |-  True && {A} // A? : false";
    "True && {A, B}   |-  True && {B} // A? : true";
    "True && {B}.{A}  |-  True && {B} // A? : true";
    "True && {A}.{B}.{C}.{D}  |-  True && {A}.{B}.{C} // C?.{D} : true";
    "True && {A}.{C}.{C}.{D}  |-  True && {A}.{B}.{C} // C?.{D} : false";
    "True && {A}.{B}.{C}.{D}  |-  True && {A}.{}.{C}.{D} // B?  : true";
    "True && {A}.{B, C}.{D}   |-  True && {A}.{C}.{D} // B?     : true";
    "True && {B, X}.{A, Y}.{B}.{Z}  |-  True && B?.{A} // {X}.{Y}.{B}.{Z} : true";
    "True && {X}.{Y}.{B}.{A, Z}     |-  True && B?.{A} // {X}.{Y}.{B}.{Z} : true";
    "True && {X}.{Y}.{B}.{A, Z}     |-  True && B?.{A} // {X}.{Y}.{B}.{Z} // {B} : false";
    "True && {B, X}.{A, Y}.{B}.{Z}  |-  True && B?.{A} // {X}.{Y}.{B}.{Z} // {B} : true";
    "True && {B, X}.{Y}.{B}.{A, Z}  |-  True && B?.{A} // {X}.{Y}.{B}.{Z} : false";
    "True && {X}.{B, Y}.{A, B}.{Z}  |-  True && B?.{A} // {X}.{Y}.{B}.{Z} : true";
    "True && {X}.{B, Y}.{B}.{A, Z}  |-  True && B?.{A} // {X}.{Y}.{B}.{Z} : false";
    "True && {X}.{Y}.{B}.{Z}.{B}.{A}  |-  True && B?.{A} // {X}.{Y}.{B}.{Z} : false";
    "True && {X}.{Y}.{B}.{Z, B}.{A}   |-  True && B?.{A} // {X}.{Y}.{B}.{Z} : false";
    "True && A?.B?.C? // {A}.{B}.{C}      |-  True && {A}.{B}.{C} : true";
    "True && A?.B?.C? // {D}.{A}.{B}.{C}  |-  True && {D}.{A}.{B}.{C} : true";
    "True && A?.B?.C? // {D}.{A}.{B}.{C}  |-  True && {A}.{A}.{B}.{C} : false";
    "True && A?.B?.C? // {D}.{A}.{B}.{C}  |-  True && {A}.{B}.{C}.{} + {A}.{B}.{}.{C} + {A}.{}.{B}.{C} + {}.{A}.{B}.{C} : true";
    "True && A?.B?.C? // {D}.{A}.{B}.{C}  |-  True && {A}.{B}.{C}.{C} + {D}.{A}.{B}.{C} : true";
    "True && {A}.{C}.B?.{D}  |-  True && {A}.B?.{D}     : true";
    "True && A?.B?.{D} // {A}.{B}.{C}   |-  True && {A}.{B}.{C, D} : true";
    "True && {A}.{B}.{C}.B?.{D}  |-  True && {A}.{B}.(B? // {C}).{D} : true";
    "True && ({A} + {B}) // {C}  |-  True && ({A} // {C}) + ({B} // {C}) : true";
    "True && A? // B?  |-  True && A?.B? + {}*.{A, B} +  B?.A? : true";
    (* Timed effects *)
    "t > 1 && {A} # t  |-  t > 3 && {A} # t : false";
    "t > 1 && {A} # t  |-  True && {A} : true";
    "t < 1 && {A} # t  |-  t < 2 && {A} # t : true";
    "t < 2 && {A} # t  |-  t < 2 && {A} # t : true";
    "t < 2 && {A} # t  |-  t < 1 && {A} # t : false";
    (* Timed Union *)
    "t < 1 && {A} # t  |-  t < 3 && {A}+{A} # t : true";
    "t < 1 && {A} # t  |-  t < 3 && {A}+{B} # t : true";
    "t > 1 && {A} # t  |-  t > 3 && {A}+{B} # t : false";
    "t < 1 && {A} # t  |-  (t1 < 3 && t2 < 3) && ({A} # t1) + ({A} # t2) : true";
    "(t1 < 1 && t2 < 1) && ({A} # t1) + ({B} # t2)  |-  t < 3 && {A}+{B} # t: true";
    "(t1 > 1 && t2 > 1) && ({A} # t1) + ({B} # t2)  |-  t > 3 && {A}+{B} # t: false";
    "(t > 3 && t1 > 1 && t2 > 1) && ({A} # t1) + ({B} # t2) # t  |-  t > 3 && {A}+{B} # t: true";
    "t < 1 && {A}+{B} # t  |-  (t1 < 2 && t2 < 2) && ({A} # t1) + ({B} # t2) : true";
    (* Timed Empty *)
    "t < 1 && {A} # t  |-  t < 3 && (emp+{A}) # t : true";
    "t < 1 && emp # t  |-  t < 3 && emp # t : true";
    "t < 1 && emp # t  |-  t < 3 && (emp+{A}) # t : true";
    "t > 3 && {A} # t  |-  t > 1 && (emp+{A}) # t : true";
    "t < 3 && {A} # t  |-  t < 1 && (emp+{A}) # t : false";
    "t > 1 && {A} # t  |-  t > 3 && (emp+{A}) # t : false";
    "t < 1 && (emp+{A}) # t  |-  t < 3 && (emp+{A}) # t : true";
    (* Timed Sequence *)
    "t > 1 && {A}.{B} # t  |-  t > 3 && {A}.{B} # t: false";
    "t < 1 && {A}.{B} # t  |-  t < 3 && {A}.{B} # t: true";
    "t < 1 && emp.{B} # t  |-  t < 3 && emp.{B} # t: true";
    "(t1 < 1 && t2 < 1) && ({A} # t1).({B} # t2)  |-  t < 3 && {A}.{B} # t: true";
    "(t1 > 1 && t2 > 1) && ({A} # t1).({B} # t2)  |-  t > 3 && {A}.{B} # t: false";
    (* Timed Empty & Sequnce & Union *)
    "(t1 < 1 && t2 < 1) && (emp+{A} # t1).{B} # t2  |-  t < 3 && {B}+{A}.{B} # t: true";
    "(t1 < 1 && t2 < 1) && {A}.(emp+{B} # t1) # t2  |-  t < 3 && {A}+{A}.{B} # t: true";
    "(t1 > 1 && t2 > 1) && (emp+{A} # t1).{B} # t2  |-  t > 3 && {B}+{A}.{B} # t: false";
    "(t1 > 1 && t2 > 1) && {A}.(emp+{B} # t1) # t2  |-  t > 3 && {A}+{A}.{B} # t: false";
    "(t1>3 && t10 > 5) && ({A} # t1).({B}#t10) |- (t2>2 && t11 > 4) && ({A}#t2).({B}#t11) : true";
    (* Timed Parallel *)
    "t < 1 && ({A} // {B}) # t  |-  t < 3 && {A} # t // {B} # t : true";
    "t < 1 && {A} # t // {B} # t  |-  t < 3 && ({A} // {B}) # t : true";
    "t < 1 && {A, B} # t  |-  t < 3 && ({A} // {B}) # t : true";
    "t < 3 && ({A} // {B}) # t  |-  t < 1 && {A} # t // {B} # t : false";
    "t > 3 && ({A} // {B}) # t  |-  t > 1 && {A} # t // {B} # t : true";
    "t > 1 && ({A} // {B}) # t  |-  t > 3 && {A} # t // {B} # t : false";
    "t < 1 && ({A}.{B} // {C}.{D}) # t  |-  t < 3 && {A}.{B} # t // {C}.{D} # t : true";
    "t > 1 && ({A}.{B} // {C}.{D}) # t  |-  t > 3 && {A}.{B} # t // {C}.{D} # t : false";
    "t < 1 && ({A}.{B} // {C}.{D}) # t  |-  (t1 < 3 && t2 < 3) && {A}.{B} # t1 // {C}.{D} # t2 : true";
    "t > 1 && ({A}.{B} // {C}.{D}) # t  |-  (t1 > 3 && t2 > 3) && {A}.{B} # t1 // {C}.{D} # t2 : false";
    (* Timed Kleene *)
    "t < 1: {A}* # t  |-  t < 3: {A}* # t :: true";
    "t < 1: {A}* # t  |-  t < 3: {A}*     :: true";
    "t < 1: {A}*      |-  t < 3: {A}* # t :: false";
    "t > 1: {A}* # t  |-  t > 3: {A}* # t :: false";
    "t < 1: {A}* # t  |-  t < 3: {A}*.{B}* # t :: true";
    "t < 1: {A}*.{B}*.{C} # t  |-  t < 3: {A}*.{B}*.{C}* # t :: true";
    "t < 1: {A}*.{B}*.{C} # t  |-  t < 3: {A}*.{B}*.{C} # t  :: true";
    "t < 1: {A}.{B}*.{C} # t   |-  t < 3: {A}*.{B}*.{C} # t  :: true";
    "t < 1: {A}*.{B}.{C} # t   |-  t < 3: {A}*.{B}*.{C} # t  :: true";
    "t < 1: {A}.{B}.{C} # t    |-  t < 3: {A}*.{B}*.{C} # t  :: true";
    "t < 1: {A}.{B}.{C}* # t   |-  t < 3: {A}*.{B}*.{C} # t  :: false";
    "t < 3: {A}* # t  |-  t < 1: {A}* # t   :: false";
    "t > 3: {A}* # t  |-  t > 1: {A}* # t   :: true";
    "t > 3: {A}* # t  |-  t > 1: {A}*       :: true";
    "t > 1: {A}* # t  |-  t > 3: {A}* # t   :: false";
    "t > 1: {A}* # t  |-  t1 > 3: {A}*      :: true";
    "t < 1: {A}* # t  |-  t1 < 3: {A}* # t1 :: true";
    "t < 1: {A}* # t  |-  (t1 < 3 && t2 < 3): ({A}* # t1).({B}* # t2) :: true";
    "t < 1: {A}* # t  |-  (t1 < 3 && t2 < 3): ({A}* # t1).({B}* # t2) :: true";
    (* Timed Await *)
    "t < 1: A? # t  |-  t < 3: A? # t  :: true";
    "t < 1: A? # t  |-  s < 3: A? # s  :: true";
    "t < 3: A? # t  |-  t < 1: A? # t  :: false";
    "t > 3: A? # t  |-  t > 1: A? # t  :: true";
    "t > 1: A? # t  |-  t > 3: A? # t  :: false";
    "t < 1: (A? # t) // ({A} # t)  |-  t < 3: {A} # t  :: true";
    "t < 1: (A? # t) // ({A} # t)  |-  s < 3: {A} # s  :: true";
    "(t1 < 1 && t2 < 1): (A? # t1) // ({A} # t2)  |-  t < 3: {A} # t  :: true";
    (* Nested Timed *)
    "(t1 < 1 && t2 < 2) && ({A} # t1) # t2  |-  t < 2 && {A} # t : true";
    "(t1 < 1 && t2 < 2) && ({A} # t1) # t2  |-  t < 1 && {A} # t : true";
    "(t1 < 2 && t2 < 3) && ({A} # t1) # t2  |-  t < 1 && {A} # t : false";
    "(t1 < 3 && t2 < 2) && ({A} # t1) # t2  |-  t < 1 && {A} # t : false";
    "(t1 < 3 && t2 < 2) && ({A} # t1) # t2  |-  t < 2 && {A} # t : true";
    "t > 3 && {A} # t  |-  (t1 > 2 && t2 > 3) && ({A} # t1) # t2 : true";
    "t > 3 && {A} # t  |-  (t1 > 2 && t2 > 3) && ({A} # t2) # t1 : true";
    "(t1 > 2 && t2 > 3) && ({A} # t1) # t2  |-  (t1 > 2 && t2 > 3) && ({A} # t1) # t2 : true";
    "(t1 > 2 && t2 > 3) && ({A} # t1) # t2  |-  (t1 > 2 && t2 > 3) && ({A} # t2) # t1 : true";
    "(t1 > 2 && t2 > 3) && ({A} # t2) # t1  |-  (t1 > 2 && t2 > 3) && ({A} # t1) # t2 : true";
    "(t1 > 2 && t2 > 3) && ({A} # t2) # t1  |-  (t1 > 2 && t2 > 3) && ({A} # t2) # t1 : true";
    (* irrelevant constraints *)
    "t < 1 && {A}  |-  t < 3 && {A} : true";
    "t < 1 && {A}  |-  (t1 < 3 && t2 < 3) && {A} + ({A}#t2) : true";
    (* Strange constraints *)
    "(d>3 && t<d) && {A} # t  |-  (d>3 && t<d) && {A} # t : true";
    (* multiple entailments *)
    "True && {A}  |-  True && {A} || True && {B} : true";
    "True && {A} || True && {B}  |-  True && {}  : true";
    "True && {A} || True && {B}  |-  True && {A} || True && {B} : true";
    (* others *)
    {|
        (0≤t ⋀ t<d ⋀ tv1≥0 ⋀ tv2≥0 ⋀ tv1+tv2=t):
         {Prep}·({Cook} # tv2)·{Ready}·{}  |-
        (0≤t ⋀ t<3): ({Prep}·{Cook} # t)·{Ready}·{Go} : false
    |};
    {|
        (0≤t ⋀ t<d ⋀ tv1≥0 ⋀ tv2≥0 ⋀ tv1+tv2=t):
         ({Prep} # tv1)·({Cook} # tv2)·{Ready}·{}  |-
        (0≤t ⋀ t<3): ({Prep}·{Cook} # t)·{Ready}·{Go} : false
    |};
    {|
        (d=3 ⋀ 0≤t ⋀ t<d ⋀ tv1≥0 ⋀ tv2≥0 ⋀ tv1+tv2=t):
         ({Prep} # tv1)·({Cook} # tv2)·{Ready}·{Go}  |-
        (0≤t ⋀ t<3): ({Prep}·{Cook} # t)·{Ready}·{Go} : true
    |};
    "t < 3: {Doing}* # t.{Done}  |-  u < 4: ({Doing} + {Other})* # u . {Done} : true";
  ]


let () =
  tests
  |> List.iteri (fun no str ->
         let case = Sleek.parse_specification str in
         let correct, verdict, history = Sleek.verify_specification case in
         Sleek.show_verification ~case ~no ~verdict ~verbose:(not correct) ~history |> print_endline;
         assert correct)
