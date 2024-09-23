open CoreAndMore

type 'a t = Term of 'a * (('a t) list)
[@@deriving eq, hash, ord, show]

let make
    (type a)
    (l:a)
    (ts:(a t) list)
  : a t =
  Term (l,ts)

module Make(S:Symbol.S) = struct
  module Symbol = S

  type 'a trm = 'a t
  [@@deriving hash, eq, ord, show]

  type t = S.t trm
  [@@deriving hash, eq, ord, show]

  let make : Symbol.t -> t list -> t = make
end
