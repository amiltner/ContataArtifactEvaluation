open CoreAndMore
open Lang
open Cta_impl


module Make
    (L : Language.S)
    (CS : FormulaExtractor.S with module Lang = L)
    (AC : AutomatonCreator.S with module Lang = L)
  : Synthesizers.GroundSketchSynthesizer.S with module L = L = struct
  module Automaton = AC.Automaton
  module GroundSketch = L.GroundSketch
  module AutsById = DictOf(Id)(Automaton)
  module L = L
  open L

  let rec make_real_loop
      ~(context:Context.t)
      ~(size:int)
      (gss:GroundSketch.t)
      (global_ufform:UFForm.t)
      (auts:AutsById.t)
      (updated_ids:Id.t list)
    : ((Id.t * Expr.t) list) option =
    Log.sketch (fun () ->
        "Updating global knowledge according to new intersections");
    let global_ufform =
      UFForm.and_
        (global_ufform::
         (List.map
            ~f:(fun id ->
                Log.sketch
                  (fun () ->
                     "Knowledge from : " ^
                     (Id.show id) ^
                     " -- " ^
                     (UFForm.show global_ufform));
                let c = AutsById.lookup_exn auts id in
                (AC.Automaton.get_final_constraints c)))
           updated_ids)
    in
    Log.sketch (fun () ->
        "Identifying mappings for each function");
    let ufform_id_term_mapping_o =
      List.fold
        ~f:(fun ufform_id_term_mapping_o (i,c) ->
            Option.bind
              ~f:(fun (ufform,id_term_mapping) ->
                  let (tin,tout,_) = List.Assoc.find_exn ~equal:Id.equal gss.holes (AC.Automaton.get_id c) in
                  let exp_f_o =
                    AC.Automaton.get_satisfying_exp_and_constraints
                      c
                      ufform
                      tin
                      tout
                  in
                  Option.map
                    ~f:(fun (exp,f) ->
                        let ufform = UFForm.band ufform f in
                        let added_id_map = (i,exp) in
                        (ufform, (added_id_map::id_term_mapping)))
                    exp_f_o)
              ufform_id_term_mapping_o)
        ~init:(Some (global_ufform,[]))
        (AutsById.as_kvp_list auts)
    in
    begin match ufform_id_term_mapping_o with
      | None ->
        Log.sketch
          (fun () -> "No mappings identified, restarting");
        None
      | Some (gen_form,id_term_mapping) ->
        Log.sketch
          (fun () -> "Possible maps identified: "
                     ^ string_of_list
                       (string_of_pair Id.show Expr.show)
                       id_term_mapping);
        let calls_in_invalids =
          List.filter_map
            ~f:(fun expr ->
                let (res,calls) =
                  Evaluator.evaluate
                    ~context
                    id_term_mapping
                    expr
                in
                let equals_true =
                  begin match res with
                    | None -> false
                    | Some v -> Value.is_true v
                  end
                in
                if equals_true then
                  None
                else
                  Some calls)
            gss.exprs
        in
        begin match calls_in_invalids with
          | [] ->
            (* Nothing was invalid, return correct values *)
            Some id_term_mapping
          | calls_in_invalid::_ ->
            let rec process_invalids invalids checker =
              begin match invalids with
                | (i,vin,vout)::t ->
                  let out_type =
                    snd (GroundSketch.get_types_exn gss i)
                  in
                  begin match
                      UFFormIntegration.call_into_ufform
                        ~context
                        ~expected_type:out_type
                        i
                        vin
                        vout with
                  | None ->
                    Log.sketch
                      (fun () ->
                         "found runtime or type error in the " ^
                         Id.show i ^ " call to " ^
                         (Value.show vin));
                    let _ = checker UFForm.Terminate in
                    [(i,vin)]
                  | Some f ->
                    begin match checker (UFForm.NextElement f) with
                      | UFForm.UserTerminated -> failwith "should not be user terminated"
                      | UFForm.Unsat core ->
                        let model = UFFormIntegration.model_into_fcs core in
                        Log.sketch
                          (fun () ->
                             "found model error: unsat core is -- " ^
                             ((string_of_list
                                 (string_of_triple Id.show Value.show Value.show))
                                model));
                        List.map ~f:(fun (i,v,vout) -> (i,v)) model
                      | Continue checker -> process_invalids t checker
                    end
                  end
                | [] ->
                  (* this should always return UFForm.UserTerminated *)
                  let _ = checker UFForm.Terminate in
                  failwith "this should not happen"
              end
            in
            Log.sketch
              (fun () ->
                 "Finding unsat core with required trace of: " ^
                 (UFForm.show gen_form));
            let small_invalid_calls =
              process_invalids
                calls_in_invalid
                (UFForm.iteratively_check gen_form)
            in
            let calls_by_id =
              group_by_keys ~is_eq:Id.equal small_invalid_calls
            in
            let updated_ids = List.map ~f:fst calls_by_id in
            let auts =
              List.fold
                ~f:(fun auts (id,callvals) ->
                    Log.sketch
                      (fun () -> "Updating automaton for " ^ (Id.show id));
                    let aut = AutsById.lookup_exn auts id in
                    let new_calls =
                      set_minus_lose_order
                        Value.compare
                        callvals
                        (Automaton.get_inputs aut)
                    in
                    let new_auts =
                      List.map
                        ~f:(fun v ->
                            let c =
                              AC.construct
                                ~context
                                ~predicate:gss.predicate
                                ~holes:gss.holes
                                ~id
                                v
                                size
                                global_ufform
                            in
                            c)
                        new_calls
                    in
                    let aut =
                      fold_on_head_exn
                        ~f:Automaton.intersect
                        (aut::new_auts)
                    in
                    AutsById.insert auts id aut)
                ~init:auts
                calls_by_id
            in
            make_real_loop
              ~context
              ~size
              gss
              global_ufform
              auts
              updated_ids
        end
    end

  let solve_element
      ~(context:Context.t)
      ~(size:int)
      (gss:GroundSketch.t)
    : ((Id.t * Expr.t) list) option =
    let learned_ufform =
      UFForm.and_
        (List.map
           ~f:(fun expr ->
               (CS.extract_formula
                  ~context
                  ~predicate:gss.predicate
                  gss.holes
                  expr
                  size))
           gss.exprs)
    in
    Log.sketch (fun () -> "Possible formulas: " ^ (UFForm.show learned_ufform));
    Log.sketch (fun () -> "Creating initial top automata");
    let auts_by_id =
      AutsById.from_kvp_list
        (List.map
           ~f:(fun i ->
               let (tin,tout) =
                 GroundSketch.get_types_exn
                   gss
                   i
               in
               (i
               ,AC.empty
                   ~context
                   ~id:i
                   ~tin
                   ~tout))
           (GroundSketch.get_hole_ids gss))
    in
    make_real_loop
      ~context
      ~size
      gss
      learned_ufform
      auts_by_id
      []

  let rec iterative_deepening_loop
      ~(context:Context.t)
      ~(size:int)
      (gss:GroundSketch.t)
    : (Id.t * Expr.t) list =
    Log.sketch
      (fun () -> "Starting solver with size " ^ (Int.to_string size));
    if (size > 10) then failwith "Error in FTA creation to debug";
    let result_option =
      solve_element
        ~context
        ~size
        gss
    in
    begin match result_option with
      | None ->
        iterative_deepening_loop
          ~context
          ~size:(size+1)
          gss
      | Some res ->
        res
    end

  let solve
      ~(context:Context.t)
      (gss:GroundSketch.t)
    : (Id.t * Expr.t) list =
    iterative_deepening_loop
      ~context
      ~size:2
      gss
end


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
    end

  let arity = snd
end

module A = Automaton.Make(Transition)(UFForm)(State)

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
    end
  in
  let _ = create_from_e exp in
  A.add_final_state a (exp,[Value.mk_true]);
  a

module AutsById = DictOf(Id)(FTACreator.C)

let call_into_ufform
    ~(context:Context.t)
    (gss:GroundSketches.t)
    (i:Id.t)
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
      let (_,expected_tout) = GroundSketches.get_types_exn gss i in
      if (Typecheck.type_equiv context.full_tc tout expected_tout) then
        Some (UFForm.fc i vin vout)
      else
        None
  end

let rec make_real_loop
    ~(context:Context.t)
    ~(size:int)
    (gss:GroundSketches.t)
    (global_ufform:UFForm.t)
    (auts:AutsById.t)
    (updated_ids:Id.t list)
  : ((Id.t * Expr.t) list) option =
  Log.sketch (fun () ->
      "Updating global knowledge according to new intersections");
  let global_ufform =
    UFForm.and_
      (global_ufform::
       (List.map
          ~f:(fun id ->
              let c = AutsById.lookup_exn auts id in
              UFForm.or_
                (List.map
                   ~f:snd
                   (FTAConstructor.A.get_finals_and_constraints c.a)))
          updated_ids))
  in
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
      (AutsById.value_list auts)
  in
  begin match ufform_id_term_mapping_o with
    | None ->
      Log.sketch
        (fun () -> "No mappings identified, restarting");
      None
    | Some (gen_form,id_term_mapping) ->
      Log.sketch
        (fun () -> "Possible maps identified: "
                   ^ string_of_list
                     (string_of_pair Id.show Expr.show)
                     id_term_mapping);
      let contextevals =
        List.map
          ~f:(fun (i,e) ->
              (i,ContextLanguage.Expr.from_standard_exp e))
          context.full_evals
      in
      let runnable_id_term_mapping =
        List.map
          ~f:(fun (i,e) -> (i,ContextLanguage.Expr.from_standard_exp e))
          id_term_mapping
      in
      let calls_in_invalids =
        List.filter_map
          ~f:(fun expr ->
              let (res,calls) =
                ContextLanguage.evaluate_with_holes
                  ~eval_context:contextevals
                  runnable_id_term_mapping
                  (ContextLanguage.Expr.from_standard_exp expr)
              in
              let equals_true =
                Option.equal ContextLanguage.Value.equal
                  res
                  (Some ContextLanguage.Value.mk_true)
              in
              if equals_true then
                None
              else
                Some calls)
          gss.exprs
      in
      let calls_in_invalids =
        List.map
          ~f:(fun cin ->
              List.map
                ~f:(fun (id,v,vout) ->
                    (id
                    ,ContextLanguage.Value.to_standard_value v
                    ,Option.map ~f:ContextLanguage.Value.to_standard_value vout))
                (ContextLanguage.EvalTree.flatten_by_height cin))
          calls_in_invalids
      in
      let calls_in_invalids =
        List.sort
          ~compare:(fun c1s c2s ->
              begin match (c1s,c2s) with
                | ((_,v1,_)::_,(_,v2,_)::_) ->
                  Int.compare (Value.size v1) (Value.size v2)
                | _ ->
                  failwith "invalid calls"
              end)
          calls_in_invalids
      in
      begin match calls_in_invalids with
        | [] ->
          (* Nothing was invalid, return correct values *)
          Some id_term_mapping
        | calls_in_invalid::_ ->
          let rec process_invalids invalids checker =
            begin match invalids with
              | (i,vin,vout)::t ->
                begin match call_into_ufform ~context gss i vin vout with
                  | None ->
                    Log.sketch
                      (fun () ->
                         "found runtime or type error in the " ^
                         Id.show i ^ " call to " ^
                         (Value.show vin));
                    let _ = checker UFForm.Terminate in
                    [(i,vin)]
                  | Some f ->
                    begin match checker (UFForm.NextElement f) with
                      | UFForm.UserTerminated -> failwith "should not be user terminated"
                      | UFForm.Unsat core ->
                        let model = List.map ~f:UFForm.destruct_fc_exn core in
                        Log.sketch
                          (fun () ->
                             "found model error: unsat core is -- " ^
                             ((string_of_list
                                 (string_of_triple Id.show Value.show Value.show))
                                model));
                        List.map ~f:(fun (i,v,vout) -> (i,v)) model
                      | Continue checker -> process_invalids t checker
                    end
                end
              | [] ->
                (* this should always return UFForm.UserTerminated *)
                let _ = checker UFForm.Terminate in
                failwith "this should not happen"
            end
          in
          Log.sketch
            (fun () ->
               "Finding unsat core with required trace of: " ^
               (UFForm.show gen_form));
          let small_invalid_calls =
            process_invalids
              calls_in_invalid
              (UFForm.iteratively_check gen_form)
          in
          let calls_by_id =
            group_by_keys ~is_eq:Id.equal small_invalid_calls
          in
          let updated_ids = List.map ~f:fst calls_by_id in
          let auts =
            List.fold
              ~f:(fun auts (id,callvals) ->
                  let aut = AutsById.lookup_exn auts id in
                  let new_calls =
                    set_minus_lose_order
                      Value.compare
                      callvals
                      aut.inputs
                  in
                  let new_auts =
                    List.map
                      ~f:(fun v ->
                          let c =
                            FTACreator.construct_fta
                              ~context
                              ~predicate:gss.predicate
                              ~holes:gss.holes
                              id
                              v
                              size
                              global_ufform
                          in
                          FTACreator.C.add_destructors c;
                          c)
                      new_calls
                  in
                  let aut =
                    fold_on_head_exn
                      ~f:FTAConstructor.intersect
                      (aut::new_auts)
                  in
                  AutsById.insert auts id aut)
              ~init:auts
              calls_by_id
          in
          make_real_loop
            ~context
            ~size
            gss
            global_ufform
            auts
            updated_ids
      end
  end

let solve_element
    ~(context:Context.t)
    ~(size:int)
    (gss:GroundSketches.t)
  : ((Id.t * Expr.t) list) option =
  Log.sketch (fun () -> "Building Sketch Automaton");
  let auts =
    List.map
      ~f:(fun expr ->
          (expr
          ,mk_from_sketch_component
              ~context
              ~predicate:gss.predicate
              gss.holes
              expr
              size))
      gss.exprs
  in
  Log.sketch (fun () -> "Identifying Finals & Constraints");
  let just_auts = List.map ~f:snd auts in
  let finals_and_constraints =
    List.map
      ~f:A.get_finals_and_constraints
      just_auts
  in
  let learned_ufform =
    UFForm.and_
      (List.map
         ~f:(fun sfs -> UFForm.or_ (List.map ~f:snd sfs))
         finals_and_constraints)
  in
  Log.sketch (fun () -> "Possible formulas: " ^ (UFForm.show learned_ufform));
  Log.sketch (fun () -> "Creating initial top automata");
  let auts_by_id =
    AutsById.from_kvp_list
      (List.map
         ~f:(fun i ->
             let (tin,tout) =
               GroundSketches.get_types_exn
                 gss
                 i
             in
             (i
             ,FTACreator.construct_empty_fta
                 ~context
                 ~id:i
                 ~tin
                 ~tout))
         (GroundSketches.get_hole_ids gss))
  in
  make_real_loop
    ~context
    ~size
    gss
    learned_ufform
    auts_by_id
    []

let rec iterative_deepening_loop
    ~(context:Context.t)
    ~(size:int)
    (gss:GroundSketches.t)
  : (Id.t * Expr.t) list =
  Log.sketch
    (fun () -> "Starting solver with size " ^ (Int.to_string size));
  if (size > 10) then failwith "Error in FTA creation to debug";
  let result_option =
    solve_element
      ~context
      ~size
      gss
  in
  begin match result_option with
    | None ->
      iterative_deepening_loop
        ~context
        ~size:(size+1)
        gss
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
    (gss:GroundSketches.t)
  : (Id.t * Expr.t) list =
  iterative_deepening_loop
    ~context
    ~size:2
    gss

module GroundSketches = GroundSketches
module L = ContataLang
module Sketch = Sketch
module UniversalFormula = UniversalFormula
