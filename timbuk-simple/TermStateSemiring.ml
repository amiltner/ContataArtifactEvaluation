open CoreAndMore

type ('a,'b) t =
  | OneOf of ('a,'b) t list
  | Transition of 'a * 'b * ('a,'b) t list
[@@deriving eq, hash, ord, show]

let false_
  : ('a,'b) t =
  OneOf []

let is_false
    (ts:('a,'b) t)
  : bool =
  begin match ts with
    | OneOf [] -> true
    | _ -> false
  end

let rec explode_one_ofs
    (ts:('a,'b) t list)
  : ('a,'b) t list =
  List.concat_map
    ~f:(fun t ->
        begin match t with
          | OneOf ts -> explode_one_ofs ts
          | _ -> [t]
        end)
    ts

let one_of
    (ts:('a,'b) t list)
  : ('a,'b) t =
  OneOf
    (List.filter
       ~f:(not % is_false)
       (explode_one_ofs ts))

let transition
    (s:'a)
    (q:'b)
    (tss:('a,'b) t list)
  : ('a,'b) t =
  if List.exists
      ~f:is_false
      tss then
    false_
  else
    Transition (s,q,tss)

(*open CoreAndMore

  type ('a,'b) t =
    TermStateDisjunctConjunct of 'a * ('b * (('a,'b) t) list) list
  [@@deriving eq, hash, ord, show]

  let create
    (type a)
    (type b)
    (symbol:a)
    (state_paths:(b * (a,b) t list))
  : (a,b) t =
  TermStateDisjunctConjunct (symbol, state_paths)
*)
