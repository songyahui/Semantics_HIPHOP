val fixpoint : f:('a -> 'a) -> ?fn_iter:('a -> unit) -> ?fn_stop:('a -> unit) -> 'a -> 'a

val opt_map2 :
  ?sn:('a -> 'a) -> ?ns:('a -> 'a) -> ss:('a -> 'a -> 'a) -> 'a option * 'a option -> 'a option
