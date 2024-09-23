module type S = sig
  include CoreAndMore.Data

  val product : t -> t -> t option

  type logic
  val logic_rep : t -> logic
end
