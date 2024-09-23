open CoreAndMore

module type S = sig
  module Lang : Language.S
  module Automaton : sig
    include Data

    val get_final_constraints : t -> UFForm.t

    val get_satisfying_exp_and_constraints
      : t ->
      UFForm.t ->
      Lang.Type.t ->
      Lang.Type.t ->
      (Lang.Expr.t * UFForm.t) option

    val get_inputs : t -> Lang.Value.t list

    val get_id : t -> Id.t

    val intersect : t -> t -> t
  end

  val empty :
    context:Lang.Context.t ->
    id:Id.t ->
    tin:Lang.Type.t ->
    tout:Lang.Type.t ->
    Automaton.t

  val construct :
    context:Lang.Context.t ->
    id:Id.t ->
    predicate:(Id.t -> Lang.Value.t -> Lang.Value.t -> bool) ->
    holes:((Id.t * (Lang.Type.t * Lang.Type.t * Id.t list)) list) ->
    Lang.Value.t ->
    int ->
    UFForm.t ->
    Automaton.t
end
