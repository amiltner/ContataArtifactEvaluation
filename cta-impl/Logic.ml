open CoreAndMore

module type Simple = sig
  include CoreAndMore.Data

  val and_ : t list -> t
  val or_ : t list -> t
  val not_ : t -> t

  val satisfiable : t -> bool
end

module type S = sig
  include CoreAndMore.Data

  val and_ : t list -> t
  val or_ : t list -> t
  val not_ : t -> t

  val satisfiable : t -> bool
  val valid : t -> bool

  val band : t -> t -> t
  val bor : t -> t -> t
  val true_ : t
  val false_ : t
  val implies : t -> t -> t

  val implication_comparison : t -> t -> CoreAndMore.partial_order_comparison
end

module FromSimple(B : Simple) : S with type t = B.t = struct
  include B

  let band x y = B.and_ [x;y]
  let bor x y = B.or_ [x;y]
  let true_ = B.and_ []
  let false_ = B.or_ []
  let implies x y = bor (B.not_ x) y

  let valid
      (f:t)
    : bool =
    not (satisfiable (not_ f))

  let implication_comparison x y =
    let x_implies_y = valid (implies x y) in
    let y_implies_x = valid (implies y x) in
    begin match (x_implies_y,y_implies_x) with
      | (true,true) -> PO_EQ
      | (true,false) -> PO_GT
      | (false,true) -> PO_LT
      | (false,false) -> PO_INCOMPARABLE
    end
end

module SubjectTo(L : S)(S : Singleton with type t = L.t) = struct
  type t = L.t
  [@@deriving eq, hash, ord, show]

  let true_ = L.true_

  let false_ = L.false_

  let bor = L.bor

  let band = L.band

  let not_ = L.not_

  let or_ = L.or_

  let and_ = L.and_

  let satisfiable (f:t) = L.satisfiable (band f S.value)

  let implies = L.implies

  let implication_comparison
      (x:t)
      (y:t)
    : partial_order_comparison =
    L.implication_comparison (band x S.value) (band y S.value)
end
