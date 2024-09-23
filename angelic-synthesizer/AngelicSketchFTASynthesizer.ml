open CoreAndMore
open Contata.Lang

module L = Contata.ContataLang

module State = struct
  type t = Expr.t * (Value.t list)
  [@@deriving eq, hash, ord, show]

  let product ((e1,vs1):t) ((e2,vs2):t) : t option =
    if Expr.equal e1 e2 then
      Some (e1,(vs1@vs2))
    else
      None
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
    | LTE
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
      | VariantSwitch _ -> 2
      | Eq _ -> 1
      | LTE -> 1
      | Abstract _ -> 1
    end

  let arity = snd
end

let simple_solve
    ~(context:Contata.Context.t)
    ~(tin:Contata.Type.t)
    ~(tout:Contata.Type.t)
  : Expr.t =
  let vout =
    Contata.Typecheck.extract_value_exn
      context
      tout
  in
  let eout = Value.to_exp vout in
  Expr.mk_func (Id.create "x", tin) eout

type func_call_req = bool * Id.t * Value.t * Value.t
[@@deriving eq, hash, ord, show]
type fcrs = func_call_req list
[@@deriving eq, hash, ord, show]

let fcrs_to_ufform (fcrs:func_call_req list) =
  Contata.UFForm.and_
    (List.map
       ~f:(fun (b,i,v1,v2) ->
           let ufform = Contata.UFForm.fc i v1 v2 in
           if b then
             ufform
           else
             Contata.UFForm.not_ ufform)
       fcrs)

module Reqs = struct
  type t = unit
  [@@deriving eq, hash, ord, show]

  let partial_compare _ _ = PO_EQ
  let false_ = ()
  let true_ = ()
  let and_ _ = ()
  let or_ _ = ()
end

module A = TimbukSimple.Automaton.Make(Transition)(State)(Reqs)
(*module F = CrazyFTASynthesizer.Create*)

let extract_rec_calls
    (ts:FTACreator.A.TermState.t)
  : (Id.t * Value.t * Value.t) list =
  let tstss =
    FTACreator.C.extract_recursive_calls
      ts
  in
  List.concat_map
    ~f:(fun (i,sin,sout) ->
        let vals_in =
          begin match FTAConstructor.State.destruct_vals sin with
            | Some (vinvouts,_) ->
              List.map ~f:snd vinvouts
            | None ->
              []
          end
        in
        let vals_out =
          begin match FTAConstructor.State.destruct_vals sout with
            | Some (vinvouts,_) ->
              List.map ~f:snd vinvouts
            | None ->
              []
          end
        in
        let inouts = List.zip_exn vals_in vals_out in
        List.map ~f:(fun (vin,vout) -> (i,vin,vout)) inouts)
    tstss

let mk_from_sketch_component
    ~(context:Contata.Context.t)
    (holes:(Id.t * (Contata.Type.t * Contata.Type.t * (Id.t list))) list)
    (exp:Expr.t)
    (global_fcrs:func_call_req list)
    (size:int)
  : A.t =
  (*let ts =
    (List.concat_map ~f:(fun (_,(tin,tout,_)) -> tout::[tin]) holes)
     @(List.map ~f:Type.mk_named (Context.keys context.tc))
     @(Context.data context.ec)
     (*@(List.map ~f:(Typecheck.typecheck_value context.ec context.tc context.vc) (List.map ~f:snd i_v))*)
  in
  let ds =
    F.C.create_ds_from_t_list_context
      ~context
      ts
    in*)
  let holes = holes in
  let a = A.empty () in
  let rec create_from_e e =
    let orig_e = e in
    begin match Expr.node e with
      | Var i ->
        let outv =
          Contata.Eval.evaluate_with_holes
            ~eval_context:context.full_evals
            e
        in
        A.add_transition
          a
          (Transition.Var i,0)
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
                          ~holes
                          i
                          v
                          size
                          (fcrs_to_ufform global_fcrs)
                      in
                      List.iter
                        ~f:(fun outv -> A.add_transition a (Transition.HoleFill i,1) [(e2,[v])] (orig_e,[outv]))
                        outs;
                      outs)
                  prior_outs
              | None ->
                List.map
                  ~f:(fun v ->
                      let outv =
                        Contata.Eval.evaluate_with_holes
                          ~eval_context:context.full_evals
                          (Expr.mk_app e1 (Value.to_exp v))
                      in
                      A.add_transition a (Transition.FunctionApp e1,1) [(e2,[v])] (orig_e,[outv]);
                      outv)
                  prior_outs
            end
          | _ ->
            List.map
              ~f:(fun v ->
                  let outv =
                    Contata.Eval.evaluate_with_holes
                      ~eval_context:context.full_evals
                      (Expr.mk_app e1 (Value.to_exp v))
                  in
                  A.add_transition a (Transition.FunctionApp e1,1) [(e2,[v])] (orig_e,[outv]);
                  outv)
              prior_outs
        end
      | Func _ -> failwith "bad2"
      | Ctor (i,e) ->
        let prior_outs = create_from_e e in
        List.map
          ~f:(fun v ->
              let outv = Value.mk_ctor i v in
              A.add_transition a (VariantConstruct i,1) [(e,[v])] (orig_e,[outv]);
              outv)
          prior_outs
      | Unctor (i,e) ->
        let prior_outs = create_from_e e in
        List.map
          ~f:(fun v ->
              let outv = snd (Value.destruct_ctor_exn v) in
              A.add_transition a (UnsafeVariantDestruct i,1) [(e,[v])] (orig_e,[outv]);
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
              A.add_transition a (Eq b,2) [(e1,[lv]);(e2,[rv])] (orig_e,[ans]);
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
              A.add_transition a (TupleConstruct len,len) instates (orig_e,[ans]);
              ans
            )
          combs
      | Proj (i,e) ->
        let prior_outs = create_from_e e in
        List.map
          ~f:(fun v ->
              let outv = List.nth_exn (Value.destruct_tuple_exn v) i in
              A.add_transition a (TupleDestruct i,1) [(e,[v])] (orig_e,[outv]);
              outv)
          prior_outs
      | Abstract (id,i) ->
        let v = Value.mk_abstract id i in
        A.add_transition
          a
          (Transition.Abstract (id,i),0)
          []
          (orig_e,[v]);
        [v]
      | LTE (e1,e2) ->
        let louts = create_from_e e1 in
        let routs = create_from_e e2 in
        cartesian_map
          ~f:(fun lv rv ->
              begin match (Value.node lv,Value.node rv) with
                | (Abstract (id1,i1),Abstract (id2,i2)) ->
                  assert (Id.equal id1 id2);
                  let ans = Value.from_bool (i1 <= i2) in
                  A.add_transition a (LTE,2) [(e1,[lv]);(e2,[rv])] (orig_e,[ans]);
                  ans
                | _ -> failwith "bad"
              end)
          louts
          routs
    end
  in
  let _ = create_from_e exp in
  A.add_final_state a (exp,[Value.mk_true]);
  a

let rec get_hole_fills
    (TermState (f,s,ts):A.TermState.t)
  : (Id.t * Value.t * Value.t) list =
  let rec_fills = List.concat_map ~f:get_hole_fills ts in
  begin match fst f with
    | HoleFill i ->
      begin match ts with
        | [TermState (_,s',_)] ->
          let ins_outs = List.zip_exn (snd s') (snd s) in
          (List.map
            ~f:(fun (inv,outv) -> (i,inv,outv))
            ins_outs)
          @rec_fills
        | _ -> failwith "issue"
      end
    | _ -> rec_fills
  end

let fcr_to_expr (b,i,v1,v2) =
  Expr.mk_eq b (Expr.mk_app (Expr.mk_var i) (Value.to_exp v1)) (Value.to_exp v2)

let fcrs_to_expr = List.map ~f:fcr_to_expr

let solve_element
    ~(context:Contata.Context.t)
    ~(global_fcrs:fcrs)
    ~(size:int)
    (s:Contata.GroundSketches.t)
  : (fcrs list,(Id.t * Expr.t) list) either =
  Contata.Log.sketch
    (fun () -> "Starting solver with global_fcrs " ^ (show_fcrs global_fcrs));
  let auts =
    List.map
      ~f:(fun expr ->
          (expr,mk_from_sketch_component
            ~context
            s.holes
            expr
            global_fcrs
            size))
      ((fcrs_to_expr global_fcrs)@s.exprs)
  in
  let tso =
    List.map
      ~f:(fun (e,a) ->
          Option.map
            ~f:(fun ts -> (e,ts))
            (A.min_term_state ~f:(fun _ -> true) ~cost:(fun _ -> 0.) ~reqs:(fun _ -> ()) ~viable_reqs:(fun () -> true) a))
      auts
  in
  begin match distribute_option tso with
    | None -> Left []
    | Some ts ->
      let hfs =
        List.concat_map
          ~f:(fun (e,ts) ->
              let hfs = get_hole_fills ts in
              Contata.Log.sketch
                (fun () ->
                   "For Expr\n\t" ^ (Expr.show e) ^
                   "\nHole Fills\n" ^
                   (String.concat
                      ~sep:"\n"
                      (List.map ~f:(fun (i,v1,v2) ->
                           ("\t" ^ Id.show i ^ ": " ^ Value.show v1 ^ " |-> " ^ Value.show v2)) hfs))
                );
              hfs)
          ts
      in
      let hfs_as_fcr =
        (List.map
           ~f:(fun (i,v1,v2) -> (true,i,v1,v2))
           hfs)
      in
      let restricted_fcrs = hfs_as_fcr@global_fcrs in
      let hfs_grouped = group_by ~key:fst3 ~equal:Id.equal hfs in
      let solns =
        List.map
          ~f:(fun vs ->
              let i = fst3 (List.hd_exn vs) in
              let all_inputs =
                List.dedup_and_sort
                  ~compare:Value.compare
                  (List.map ~f:snd3 vs)
              in
              let cs =
                List.map
                  ~f:(fun v ->
                      let c =
                        (FTACreator.C.copy
                           (FTACreator.construct_fta
                              ~context
                              ~holes:s.holes
                              i
                              v
                              size
                              (fcrs_to_ufform restricted_fcrs)))
                      in
                      FTACreator.C.add_destructors c;
                      (*let ts = Option.value_exn (FTACreator.C.min_term_state c (fun _ -> true)) in
                      let t = TimbukSimple.TermState.to_term ts in
                      let cte = FTACreator.C.term_to_contextful_exp i (Contata.Type.mk_tuple []) (Contata.Type.mk_tuple []) t in
                        print_endline (ContextLanguage.Expr.show cte);*)
                      c)
                  all_inputs
              in
              let intersected_c =
                fold_on_head_exn
                  ~f:FTACreator.C.intersect
                  cs
              in
              let (tin,tout,_) = List.Assoc.find_exn ~equal:Id.equal s.holes i in
              let tso = FTACreator.C.min_term_state intersected_c (fun _ -> true) in
              Contata.Log.sketch
                (fun () ->
                   let kvps = List.map ~f:(fun (_,vin,vout) -> (vin,vout)) vs in
                   "Input-Output spec for " ^ (Id.show i) ^ "\n" ^
                   (String.concat
                      ~sep:"\n"
                      (List.map
                         ~f:(fun (vin,vout) ->
                             "\t" ^ (Value.show vin) ^ " |-> " ^ (Value.show vout))
                         kvps)));
              let ans =
                Option.map
                  ~f:(fun ts ->
                      let t = TimbukSimple.TermState.to_term ts in
                      (i,FTACreator.C.term_to_contextful_exp i tin tout t,ts))
                  tso
              in
              Contata.Log.sketch
                (fun () ->
                   begin match ans with
                     | Some (i,e,ts) -> (Id.show i) ^ " was generated with expression " ^ (Expr.show (ContextLanguage.Expr.to_standard_exp e))
                     | None ->
                       (Id.show i) ^ " had no solution"
                   end);
              ans
              (*let all_inputs = List.map ~f:fst inouts in
                (i,snd (F.synth
                        (F.init
                           ~problem:(Problem.dummy_of_context context)
                           ~context:context
                           ~id:i
                           ~tin
                           ~tout)
                        all_inputs
                        (fun v1 v2 ->
                           begin match List.Assoc.find ~equal:Value.equal inouts v1 with
                             | None -> true
                             | Some v2s -> List.for_all ~f:(Value.equal v2) v2s
                           end)))*))
          hfs_grouped
      in
      begin match distribute_option solns with
        | None ->
          Left
            (List.map
               ~f:(fun (i,vin,vout) ->
                   (false,i,vin,vout)::
                   global_fcrs)
               hfs)
        | Some solns ->
          (* check solns are correct *)
          let i_es = List.map ~f:(fun (i,e,_) -> (i,e)) solns in
          let i_es =
            i_es@
            List.filter_map
              ~f:(fun (i,(tin,tout,calls)) ->
                  begin match List.Assoc.find ~equal:Id.equal i_es i with
                    | None -> Some (i,ContextLanguage.Expr.from_standard_exp (simple_solve ~context ~tin ~tout))
                    | Some _ -> None
                  end)
              s.holes
          in
          let contextevals =
            List.map
              ~f:(fun (i,e) ->
                  (i,ContextLanguage.Expr.from_standard_exp e))
              context.full_evals
          in
          let results =
            List.map
              ~f:(fun expr ->
                  ContextLanguage.safe_evaluate_with_holes
                    ~eval_context:(contextevals)
                    i_es
                    (ContextLanguage.Expr.from_standard_exp expr))
              s.exprs
          in
          if List.for_all ~f:(fun v -> Option.equal ContextLanguage.Value.equal v (Some ContextLanguage.Value.mk_true)) results then
            (* desired found *)
            Right (List.map ~f:(fun (i,e) -> (i,ContextLanguage.Expr.to_standard_exp e)) i_es)
          else
            (* desired not actually found, look for other outputs *)
            let other_outputs_restriction =
              (List.map
                 ~f:(fun (i,vin,vout) ->
                     (false,i,vin,vout)::
                     global_fcrs)
                 hfs)
            in
            (* or strengthen rec calls *)
            let rec_calls =
              List.concat_map
                ~f:extract_rec_calls
                (List.map ~f:trd3 solns)
            in
            let rec_call_eval_restricted =
              List.map ~f:(fun (i,v1,v2) -> (true,i,v1,v2)) rec_calls
              @restricted_fcrs
            in
            (* or require different rec calls *)
            let other_rec_calls_restricted =
              List.map ~f:(fun (i,v1,v2) -> (false,i,v1,v2)::restricted_fcrs) rec_calls
            in
            Left
              (rec_call_eval_restricted::other_rec_calls_restricted@other_outputs_restriction)
      end
  end

let rec solve_loop
    ~(context:Contata.Context.t)
    ~(global_fcrs:fcrs list)
    ~(size:int)
    (s:Contata.GroundSketches.t)
  : ((Id.t * Expr.t) list) option =
  begin match global_fcrs with
    | [] -> None
    | h::t ->
      let res =
        solve_element
          ~context
          ~global_fcrs:h
          ~size
          s
      in
      begin match res with
        | Left more -> solve_loop ~context ~global_fcrs:(t@more) ~size s
        | Right soln -> Some soln
      end
  end

let rec iterative_deepening_loop
    ~(context:Contata.Context.t)
    ~(size:int)
    (s:Contata.GroundSketches.t)
  : (Id.t * Expr.t) list =
  Contata.Log.sketch
    (fun () -> "Starting solver with size " ^ (Int.to_string size));
  let result_option =
    solve_loop
      ~context
      ~global_fcrs:[[]]
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

let solve
    ~(context:Contata.Context.t)
    (s:L.GroundSketch.t)
  : (Id.t * Expr.t) list =
  if List.is_empty s.exprs then
    begin
      Contata.Log.sketch
        (fun () -> "Trivial Ground Sketch, simple solver enabled.");
      List.map
        ~f:(fun (i,(tin,tout,calls)) ->
            (i,simple_solve ~context ~tin ~tout))
        s.holes
    end
  else
    let res =
      begin
        Contata.Log.sketch
          (fun () -> "Nontrivial Ground Sketch, full solver enabled.");
        iterative_deepening_loop
          ~context
          ~size:2
          s
      end
    in
    res@
    List.filter_map
      ~f:(fun (i,(tin,tout,calls)) ->
          begin match List.Assoc.find ~equal:Id.equal res i with
            | None -> Some (i,simple_solve ~context ~tin ~tout)
            | Some _ -> None
          end)
      s.holes

