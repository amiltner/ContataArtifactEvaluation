open CoreAndMore

type ('a,'b,'c) t =
  | OneOf of ('a,'b,'c) t list
  | Transition of 'a * 'b * 'c * ('a,'b,'c) t list
  | FinalLogic of 'c * ('a,'b,'c) t
[@@deriving eq, hash, ord, show]

let false_
  : ('a,'b,'c) t =
  OneOf []

let is_false
    (ts:('a,'b,'c) t)
  : bool =
  begin match ts with
    | OneOf [] -> true
    | _ -> false
  end

let rec explode_one_ofs
    (ts:('a,'b,'c) t list)
  : ('a,'b,'c) t list =
  List.concat_map
    ~f:(fun t ->
        begin match t with
          | OneOf ts -> explode_one_ofs ts
          | _ -> [t]
        end)
    ts

let one_of
    (ts:('a,'b,'c) t list)
  : ('a,'b,'c) t =
  let cands =
    List.filter
      ~f:(not % is_false)
      (explode_one_ofs ts)
  in
  begin match cands with
    | [cand] -> cand
    | _ -> OneOf cands
  end

let transition
    (s:'a)
    (q:'b)
    (f:'c)
    (tss:('a,'b,'c) t list)
  : ('a,'b,'c) t =
  if List.exists
      ~f:is_false
      tss then
    false_
  else
    Transition (s,q,f,tss)

let final_logic
    (f:'c)
    (tss:('a,'b,'c) t)
  : ('a,'b,'c) t =
  FinalLogic (f,tss)

let rec to_term
    (tss:('a,'b,'c) t)
  : 'a Term.t =
  begin match tss with
    | OneOf tsss -> to_term (List.hd_exn tsss)
    | Transition (l,_,_,vs) ->
      Term (l,List.map ~f:to_term vs)
    | FinalLogic (_,t) -> to_term t
  end

let rec to_logic
    (and_:'c list -> 'c)
    (or_:'c list -> 'c)
    (tss:('a,'b,'c) t)
  : 'c =
  let to_logic_simple = to_logic and_ or_ in
  begin match tss with
    | OneOf tsss -> or_ (List.map ~f:to_logic_simple tsss)
    | Transition (_,_,q,vs) ->
      and_ (q::(List.map ~f:to_logic_simple vs))
    | FinalLogic (f,tss) ->
      and_ [f;to_logic_simple tss]
  end

module Make(T:Data)(Q:Data)(L:Logic.S) = struct
  module Symbol = T
  module State = Q
  module Logic = L

  type ('a,'b,'c) tss = ('a,'b,'c) t
  [@@deriving hash, eq, ord, show]

  type t = (T.t,Q.t,L.t) tss

  let false_ : t = false_

  let is_false : t -> bool = is_false

  let explode_one_ofs : t list -> t list = explode_one_ofs

  let one_of : t list -> t = one_of

  let transition : T.t -> Q.t -> L.t -> t list -> t = transition

  let final_logic : L.t -> t -> t = final_logic

  let to_term : t -> Symbol.t Term.t = to_term

  let to_logic : t -> Logic.t = to_logic Logic.and_ Logic.or_
end
