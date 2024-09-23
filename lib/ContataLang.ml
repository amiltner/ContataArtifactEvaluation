open CoreAndMore

module Context = Context
module Expr = Lang.Expr
module Value = struct
  include Lang.Value

  let is_true = equal true_
end
module Type = Type
module Param = Param
module Evaluator = struct
  let evaluate
      ~(context:Context.t)
      (new_context:(Id.t * Expr.t) list)
      (e:Expr.t)
    : Value.t option * (Id.t * Value.t * Value.t option) list =
    let contextevals =
      List.map
        ~f:(fun (i,e) ->
            (i,ContextLanguage.Expr.from_standard_exp e))
        context.full_evals
    in
    let runnable_id_term_mapping =
      List.map
        ~f:(fun (i,e) -> (i,ContextLanguage.Expr.from_standard_exp e))
        new_context
    in
    let (vo,et) =
      ContextLanguage.evaluate_with_holes
        ~eval_context:contextevals
        runnable_id_term_mapping
        (ContextLanguage.Expr.from_standard_exp e)
    in
    let vo = Option.map ~f:ContextLanguage.Value.to_standard_value vo in
    let flattened =
      ContextLanguage.EvalTree.flatten_by_height et
    in
    let flattened =
      List.map
        ~f:(fun (i,v,vo) ->
            (i
            ,ContextLanguage.Value.to_standard_value v
            ,Option.map ~f:ContextLanguage.Value.to_standard_value vo))
        flattened
    in
    (vo,flattened)
end

module UFFormIntegration = struct
  let call_into_ufform
      ~(context:Context.t)
      ~(expected_type:Type.t)
      (id:Id.t)
      (vin:Value.t)
      (vout:Value.t option)
    : UFForm.t option =
    begin match vout with
      | None -> None
      | Some vout ->
        let tout =
          Typecheck.typecheck_value
            context.full_ec
            context.full_tc
            context.full_vc
            vout
        in
        if (Typecheck.type_equiv context.full_tc tout expected_type) then
          Some (UFForm.fc id vin vout)
        else
          None
    end

  let model_into_fcs
      (model:UFForm.t list)
    : (Id.t * Value.t * Value.t) list =
    List.map ~f:UFForm.destruct_fc_exn model
end

module UniversalFormula = UniversalFormula
module Sketch = Sketch
module GroundSketch = GroundSketches
