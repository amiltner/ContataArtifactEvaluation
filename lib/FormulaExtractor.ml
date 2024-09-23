open CoreAndMore

module type S = sig
  module Lang : Language.S

  val extract_formula :
    context:Lang.Context.t ->
    predicate:(Id.t -> Lang.Value.t -> Lang.Value.t -> bool) ->
    (Id.t * (Lang.Type.t * Lang.Type.t * (Id.t list))) list ->
    Lang.Expr.t ->
    int ->
    UFForm.t
end
