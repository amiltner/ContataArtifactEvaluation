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
