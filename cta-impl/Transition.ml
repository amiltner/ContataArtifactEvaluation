type ('a,'b,'c) t =
  {
    configuration : ('a,'b,'c) Configuration.t ;
    target        : 'c                         ;
  }
[@@deriving eq, hash, ord, show]
