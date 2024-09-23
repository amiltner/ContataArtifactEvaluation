module type S = sig
  include CoreAndMore.Data

  val arity : t -> int
end
