open CoreAndMore

module type S = sig
  module Context : sig
    include Data
  end
  module Expr : sig
    include Data
  end
  module Value : sig
    include Data

    val to_exp : t -> Expr.t

    val is_true : t -> bool
  end
  module Type : sig
    include Data
  end
  module Param : sig
    include Data with type t = Id.t * Type.t
  end
  module UniversalFormula : sig
    include Data with type t = ((Id.t * Type.t) list * Expr.t)
  end
  module Sketch : sig
    type t =
      {
        holes     : (Id.t * (Type.t * Type.t * Id.t list)) list ;
        forms     : UniversalFormula.t list                     ;
        predicate : Id.t -> Value.t -> Value.t -> bool          ;
      }

    val pp : t pper
    val show : t shower
  end
  module GroundSketch : sig
    type t =
      {
        holes     : (Id.t * (Type.t * Type.t * Id.t list)) list ;
        predicate : Id.t -> Value.t -> Value.t -> bool          ;
        exprs     : Expr.t list                                 ;
      }

    val pp : t pper
    val show : t shower

    val from_sketch : Sketch.t -> t

    val integrate_uf_and_inputs :
      t ->
      UniversalFormula.t ->
      (Id.t * Value.t) list ->
      t

    val get_hole_ids : t -> Id.t list

    val get_types_exn : t -> Id.t -> (Type.t * Type.t)

    val get_hole_info : t -> Id.t -> (Type.t * Type.t * (Id.t list))
  end
  module Evaluator : sig
    val evaluate : Expr.t -> Value.t

    val evaluate :
      context:Context.t ->
      (Id.t * Expr.t) list ->
      Expr.t ->
      (Value.t option * (Id.t * Value.t * Value.t option) list)
  end
  module UFFormIntegration : sig
    val call_into_ufform :
      context:Context.t ->
      expected_type:Type.t ->
      Id.t ->
      Value.t ->
      Value.t option ->
      UFForm.t option

    val model_into_fcs :
      UFForm.t list ->
      (Id.t * Value.t * Value.t) list
  end
end
