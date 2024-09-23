open CoreAndMore
open Lang
open Cta_impl

module L = ContataLang

module State = struct
  type t = Expr.t * (Value.t list)
  [@@deriving eq, hash, ord, show]

  let product ((e1,vs1):t) ((e2,vs2):t) : t option =
    if Expr.equal e1 e2 then
      Some (e1,(vs1@vs2))
    else
      None

  type logic = UFForm.t

  let logic_rep x = UFForm.true_
end

module Transition = struct
  type id =
    | FunctionApp of Expr.t
    | Apply
    | VariantConstruct of Id.t
    | UnsafeVariantDestruct of Id.t
    | TupleConstruct of int
    | TupleDestruct of int
    | Var of Id.t
    | LetIn
    | AngelicCall of Id.t
    | HoleFill of Id.t
    | VariantSwitch of Id.t list
    | Eq of bool
    | Func of Param.t * Expr.t
    | Abstract of Id.t * int
  [@@deriving eq, hash, ord, show]
  type t = (id * int)
  [@@deriving eq, hash, ord, show]

  let cost
      (x:t)
    : int =
    begin match fst x with
      | FunctionApp _ -> 1
      | Apply -> 0
      | VariantConstruct _ -> 2
      | UnsafeVariantDestruct _ -> 1
      | TupleConstruct _ -> 1
      | TupleDestruct _ -> 1
      | Var _ -> 0
      | LetIn -> 0
      | AngelicCall _ -> 1
      | HoleFill _ -> 1
      | Func _ -> 1
      | VariantSwitch _ -> 2
      | Eq _ -> 1
      | Abstract _ -> 1
    end

  let arity = snd
end

module A = Cta_impl.Automaton.Make(Transition)(UFForm)(State)

let mk_from_sketch_component
    ~(context:Context.t)
    ~(predicate:Id.t -> Value.t -> Value.t -> bool)
    (holes:(Id.t * (Type.t * Type.t * (Id.t list))) list)
    (exp:Expr.t)
    (size:int)
  : A.t =
  let holes = holes in
  let a = A.empty () in
  let rec create_from_e e =
    let orig_e = e in
    begin match Expr.node e with
      | Var i ->
        let outv =
          Eval.evaluate_with_holes
            ~eval_context:context.full_evals
            e
        in
        A.add_transition
          a
          (Transition.Var i,0)
          UFForm.true_
          []
          (orig_e,[outv]);
        [outv]
      | App (e1,e2) ->
        let prior_outs = create_from_e e2 in
        begin match Expr.node e1 with
          | Var i ->
            begin match List.Assoc.find ~equal:Id.equal holes i with
              | Some (tin,tout,calls) ->
                List.concat_map
                  ~f:(fun v ->
                      let outs =
                        FTACreator.get_finals
                          ~context
                          ~predicate
                          ~holes
                          i
                          v
                          size
                          UFForm.true_
                      in
                      List.iter
                        ~f:(fun outv ->
                            A.add_transition
                              a
                              (Transition.HoleFill i,1)
                              (snd outv)
                              [(e2,[v])]
                              (orig_e,[fst outv]))
                        outs;
                      List.map ~f:fst outs)
                  prior_outs
              | None ->
                List.map
                  ~f:(fun v ->
                      let outv =
                        Eval.evaluate_with_holes
                          ~eval_context:context.full_evals
                          (Expr.mk_app e1 (Value.to_exp v))
                      in
                      A.add_transition
                        a
                        (Transition.FunctionApp e1,1)
                        UFForm.true_
                        [(e2,[v])]
                        (orig_e,[outv]);
                      outv)
                  prior_outs
            end
          | _ ->
            List.map
              ~f:(fun v ->
                  let outv =
                    Eval.evaluate_with_holes
                      ~eval_context:context.full_evals
                      (Expr.mk_app e1 (Value.to_exp v))
                  in
                  A.add_transition a (Transition.FunctionApp e1,1) UFForm.true_ [(e2,[v])] (orig_e,[outv]);
                  outv)
              prior_outs
        end
      | Func (p,e) ->
        let outv =
          Eval.evaluate_with_holes
            ~eval_context:context.full_evals
            orig_e
        in
        A.add_transition
          a
          (Transition.Func (p,e),0)
          UFForm.true_
          []
          (orig_e,[outv]);
        [outv]
      | Ctor (i,e) ->
        let prior_outs = create_from_e e in
        List.map
          ~f:(fun v ->
              let outv = Value.mk_ctor i v in
              A.add_transition a (VariantConstruct i,1) UFForm.true_ [(e,[v])] (orig_e,[outv]);
              outv)
          prior_outs
      | Unctor (i,e) ->
        let prior_outs = create_from_e e in
        List.map
          ~f:(fun v ->
              let outv = snd (Value.destruct_ctor_exn v) in
              A.add_transition a (UnsafeVariantDestruct i,1) UFForm.true_ [(e,[v])] (orig_e,[outv]);
              outv)
          prior_outs
      | Eq (b,e1,e2) ->
        let louts = create_from_e e1 in
        let routs = create_from_e e2 in
        cartesian_map
          ~f:(fun lv rv ->
              let ans =
                if Value.equal lv rv then
                  (Value.from_bool b)
                else
                  (Value.from_bool (not b))
              in
              A.add_transition a (Eq b,2) UFForm.true_ [(e1,[lv]);(e2,[rv])] (orig_e,[ans]);
              ans)
          louts
          routs
      | Match _ -> failwith "no too hard"
      | Fix _ -> failwith "no too hard"
      | Tuple es ->
        let eouts =
          List.map
            ~f:(fun e ->
                List.map
                  ~f:(fun v -> (e,v))
                  (create_from_e e))
            es
        in
        let combs =
          combinations
            eouts
        in
        let len = List.length es in
        List.map
          ~f:(fun eouts ->
              let ans = Value.mk_tuple (List.map ~f:snd eouts) in
              let instates = List.map ~f:(fun (e,v) -> (e,[v])) eouts in
              A.add_transition a (TupleConstruct len,len) UFForm.true_ instates (orig_e,[ans]);
              ans
            )
          combs
      | Proj (i,e) ->
        let prior_outs = create_from_e e in
        List.map
          ~f:(fun v ->
              let outv = List.nth_exn (Value.destruct_tuple_exn v) i in
              A.add_transition a (TupleDestruct i,1) UFForm.true_ [(e,[v])] (orig_e,[outv]);
              outv)
          prior_outs
      | Abstract (id,i) ->
        let v = Value.mk_abstract id i in
        A.add_transition
          a
          (Transition.Abstract (id,i),0)
          UFForm.true_
          []
          (orig_e,[v]);
        [v]
    end
  in
  let _ = create_from_e exp in
  A.add_final_state a (exp,[Value.mk_true]);
  a

let extract_formula
    ~(context:Context.t)
    ~(predicate:Id.t -> Value.t -> Value.t -> bool)
    (holes:(Id.t * (Type.t * Type.t * Id.t list)) list)
    (e:Expr.t)
    (size:int)
  : UFForm.t =
  Log.sketch (fun () -> "Making sketch components");
  let aut =
    mk_from_sketch_component
      ~context
      ~predicate
      holes
      e
      size
  in
  Log.sketch (fun () -> "Identifying Finals & Constraints");
  let finals_and_constraints = A.get_finals_and_constraints aut in
  UFForm.or_ (List.map ~f:snd finals_and_constraints)

let rec solve_simple
    ~(context:Context.t)
    ~(size:int)
    (gss:L.GroundSketch.t)
  : ((Id.t * Expr.t) list) option =
  FTACreator.M.result_storage := FTACreator.M.ResultDict.empty;
  let learned_ufform =
    UFForm.and_
      (List.map
         ~f:(fun expr ->
             (extract_formula
                ~context
                ~predicate:gss.predicate
                gss.holes
                expr
                size))
         gss.exprs)
  in
  Log.sketch (fun () -> "Possible formulas: " ^ (UFForm.show learned_ufform));
  let all_ins = FTACreator.M.ResultDict.as_kvp_list !FTACreator.M.result_storage in
  let kvps =
    List.map
      ~f:(fun (inv,outc) ->
          (inv.id, outc))
      all_ins
  in
  let grouped = group_by_keys ~is_eq:Id.equal kvps in
  let (intersections,possible) =
    List.unzip
      (List.map
         ~f:(fun (id,outcs) ->
             let intersected =
               fold_on_head_exn
                 ~f:FTAConstructor.intersect
                 outcs
             in
             let possible =
               UFForm.or_
                 (List.map
                    ~f:snd
                    (FTAConstructor.A.get_finals_and_constraints intersected.a))
             in
             (intersected,possible))
         grouped)
  in
  let global_ufform = UFForm.or_ (learned_ufform::possible) in
  Log.sketch (fun () ->
      "Identifying mappings for each function");
  let ufform_id_term_mapping_o =
    List.fold
      ~f:(fun ufform_id_term_mapping_o c ->
          Option.bind
            ~f:(fun (ufform,id_term_mapping) ->
                let ts_option =
                  FTACreator.C.min_term_state
                    c
                    ufform
                in
                Option.map
                  ~f:(fun ts ->
                      let term = TermState.to_term ts in
                      let f = FTACreator.C.A.all_accepting_logic c.a term in
                      let ufform = UFForm.band ufform f in
                      let (tin,tout,_) = List.Assoc.find_exn ~equal:Id.equal gss.holes c.id in
                      let exp =
                        ContextLanguage.Expr.to_standard_exp
                          (FTACreator.C.term_to_contextful_exp c.id tin tout term)
                      in
                      let added_id_map = (c.id,exp) in
                      (ufform, (added_id_map::id_term_mapping)))
                  ts_option)
            ufform_id_term_mapping_o)
      ~init:(Some (global_ufform,[]))
      intersections
  in
  Option.map ~f:snd ufform_id_term_mapping_o

let rec iterative_deepening_loop
    ~(context:Context.t)
    ~(size:int)
    (s:L.GroundSketch.t)
  : (Id.t * Expr.t) list =
  Log.sketch
    (fun () -> "Starting solver with size " ^ (Int.to_string size));
  let result_option =
    solve_simple
      ~context
      ~size
      s
  in
  begin match result_option with
    | None ->
      iterative_deepening_loop
        ~context
        ~size:(size+1)
        s
    | Some res ->
      res
  end

let simple_solve
    ~(context:Context.t)
    ~(tin:Type.t)
    ~(tout:Type.t)
  : Expr.t =
  let vout =
    Typecheck.extract_value_exn
      context
      tout
  in
  let eout = Value.to_exp vout in
  Expr.mk_func (Id.create "x", tin) eout

let solve
    ~(context:Context.t)
    (gss:L.GroundSketch.t)
  : (Id.t * Expr.t) list =
  if List.is_empty gss.exprs then
    begin
      Log.sketch
        (fun () -> "Trivial Ground Sketch, simple solver enabled.");
      List.map
        ~f:(fun (i,(tin,tout,calls)) ->
            (i,simple_solve ~context ~tin ~tout))
        gss.holes
    end
  else
    let res =
      begin
        Log.sketch
          (fun () -> "Nontrivial Ground Sketch, full solver enabled.");
        iterative_deepening_loop
          ~context
          ~size:2
          gss
      end
    in
    res@
    List.filter_map
      ~f:(fun (i,(tin,tout,calls)) ->
          begin match List.Assoc.find ~equal:Id.equal res i with
            | None -> Some (i,simple_solve ~context ~tin ~tout)
            | Some _ -> None
          end)
      gss.holes
