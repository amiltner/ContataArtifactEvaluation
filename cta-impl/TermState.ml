open CoreAndMore

type ('a,'b) t = TermState of 'a * 'b * (('a,'b) t) list
[@@deriving eq, hash, ord, show]

let rec to_term
    (TermState (t,_,tss):('a,'b) t)
  : 'a Term.t =
  Term (t,List.map ~f:to_term tss)

let get_state
    (TermState (_,s,_):('a,'b) t)
  : 'b =
  s

module Make(L:Symbol.S)(Q:State.S) = struct
  module Symbol = L
  module State = Q

  type ('a,'b) ts = ('a,'b) t
  [@@deriving eq, hash, ord, show]

  type t = (L.t,Q.t) ts
  [@@deriving eq, hash, ord, show]

  let to_term : (L.t,Q.t) ts -> L.t Term.t = to_term

  let get_state : (L.t,Q.t) ts -> Q.t = get_state
end
