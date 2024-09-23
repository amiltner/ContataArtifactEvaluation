open CoreAndMore

type 'a t = Term of 'a * (('a t) list)
[@@deriving eq, hash, ord, show]
