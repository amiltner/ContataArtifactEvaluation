open CoreAndMore

module type S = sig
  include CoreAndMore.Data

  module State : State.S
  module Symbol : Symbol.S
  module Logic : Logic.S

  val product : t -> t -> t option

  val make : sources:(State.t list) -> label:Symbol.t -> constrt:Logic.t -> t

  val get_sources : t -> State.t list
  val get_label : t -> Symbol.t
  val get_constrt : t -> Logic.t
end

type ('a,'b,'c) t =
  {
    sources : 'a list;
    label   : 'b;
    constrt : 'c;
  }
[@@deriving eq, hash, ord, show]

let make
    ~(sources:'a list)
    ~(label:'b)
    ~(constrt:'c)
  : ('a,'b,'c) t =
  {
    sources;
    label;
    constrt;
  }

let product
    (type a)
    (type b)
    (type c)
    ~(state_equal:a -> a -> bool)
    ~(symbol_equal:b -> b -> bool)
    ~(logic_equal:c -> c -> bool)
    ~(state_product:a -> a -> a option)
    ~(logic_band:c -> c -> c)
    (c1:(a,b,c) t)
    (c2:(a,b,c) t)
  : ((a,b,c) t) option =
  if equal state_equal symbol_equal logic_equal c1 c2 then
    Some c1
  else
  if symbol_equal c1.label c2.label then
    let label = c1.label in
    begin match CoreAndMore.distribute_option (List.map2_exn ~f:state_product c1.sources c2.sources) with
      | None -> None
      | Some sources ->
        let constrt = logic_band c1.constrt c2.constrt in
        Some (make ~label ~sources ~constrt)
    end
  else
    None

module Make(Q : State.S)(F : Symbol.S)(L : Logic.S) : S
  with type t = (Q.t,F.t,L.t) t
   and module State = Q
   and module Symbol = F
   and module Logic = L = struct

  type ('a,'b,'c) confg = ('a,'b,'c) t
  [@@deriving eq, hash, ord, show]

  type t = (Q.t,F.t,L.t) confg
  [@@deriving eq, hash, ord, show]

  module State = Q
  module Symbol = F
  module Logic = L

  let make = make

  let product =
    product
      ~state_equal:State.equal
      ~symbol_equal:Symbol.equal
      ~logic_equal:Logic.equal
      ~state_product:State.product
      ~logic_band:Logic.band

  let get_sources c = c.sources

  let get_label c = c.label

  let get_constrt c = c.constrt
end
