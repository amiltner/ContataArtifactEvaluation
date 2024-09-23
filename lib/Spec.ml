open CoreAndMore
open Lang

type t =
  | IO of Id.t * Expr.t * Expr.t
  | Post of (Id.t * Expr.t)
  | Equiv of (Id.t * Expr.t)
  | Test of UniversalFormula.t
[@@deriving eq, hash, ord, show]

module IdHash = HashTable.Make(Id)

let to_single_pred
    ~(context:Context.t)
    (s:t)
  : Value.t -> Value.t -> bool =
  begin match s with
    | IO (_,e1,e2) ->
      let v1 = Eval.evaluate_with_holes ~eval_context:context.full_evals e1 in
      let v2 = Eval.evaluate_with_holes ~eval_context:context.full_evals e2 in
      fun inv ->
        if Value.equal inv v1 then
          fun outv -> Value.equal outv v2
        else
          fun _ -> true
    | Post (_,e) ->
      (fun v1 v2 ->
         let e1 = Value.to_exp v1 in
         let e2 = Value.to_exp v2 in
         let full_exp = Expr.mk_app (Expr.mk_app e e1) e2 in
         let vout =
           Eval.safe_evaluate_with_holes
             ~eval_context:context.full_evals
             full_exp
         in
         begin match vout with
           | None -> false
           | Some vout -> Value.equal vout Value.mk_true
         end)
    | Equiv (_,e) ->
      (fun v1 v2 ->
         let e1 = Value.to_exp v1 in
         let e2 = Value.to_exp v2 in
         let full_exp = Expr.mk_equal (Expr.mk_app e e1) e2 in
         let vout =
           Eval.safe_evaluate_with_holes
             ~eval_context:context.full_evals
             full_exp
         in
         begin match vout with
           | None -> false
           | Some vout -> Value.equal vout Value.mk_true
         end)
    | Test _ -> failwith "cannot do relational"
  end

let to_postcondition_predicate
    ~(context:Context.t)
    (ss:t list)
  : Id.t -> Value.t -> Value.t -> bool =
  let id_spec_tbl = IdHash.empty () in
  let add_if_nonempty x lo =
    begin match lo with
      | None -> [x]
      | Some l -> x::l
    end
  in
  List.iter
    ~f:(fun s ->
        begin match s with
          | IO (i,_,_) -> IdHash.update i (add_if_nonempty s) id_spec_tbl
          | Post (i,_) -> IdHash.update i (add_if_nonempty s) id_spec_tbl
          | Equiv (i,_) -> IdHash.update i (add_if_nonempty s) id_spec_tbl
          | Test _ -> ()
        end)
    ss;
  let id_filter_tbl =
    IdHash.map
      ~f:(fun ss ->
          let all_preds =
            List.map
              ~f:(to_single_pred ~context)
              ss
          in
          fun vin -> fun vout -> List.for_all ~f:(fun p -> p vin vout) all_preds)
      id_spec_tbl
  in
  fun id ->
    IdHash.find_default
      ~default:(fun vin -> fun vout -> true)
      id
      id_filter_tbl

let to_uf
    (s:t)
    ~(input_types:Id.t -> Type.t)
  : UniversalFormula.t =
  begin match s with
    | IO (i,ein,eout) ->
      let e =
        Expr.mk_equal
          (Expr.mk_app (Expr.mk_var i) ein)
          eout
      in
      ([],e)
    | Post (i,epost) ->
      let ((input_i,input_t),_) = Expr.destruct_func_exn epost in
      let input_e = Expr.mk_var input_i in
      let func_e = Expr.mk_var i in
      let e =
        Expr.mk_app
          (Expr.mk_app
             epost
             input_e)
          (Expr.mk_app func_e input_e)
      in
      ([(input_i,input_t)],e)
    | Equiv (i,e) ->
      let xid = Id.create "x" in
      let xvar = Expr.mk_var xid in
      let e =
        Expr.mk_equal
          (Expr.mk_app (Expr.mk_var i) xvar)
          (Expr.mk_app e xvar)
      in
      ([(xid,input_types i)],e)
    | Test uf -> uf
  end

let to_pred_and_tests
    ~(context:Context.t)
    ~(input_types:Id.t -> Type.t)
    (ss:t list)
  : (Id.t -> Value.t -> Value.t -> bool) * UniversalFormula.t list =
  let pred = to_postcondition_predicate ~context ss in
  let ufs = List.map ~f:(to_uf ~input_types) ss in
  (pred,ufs)
