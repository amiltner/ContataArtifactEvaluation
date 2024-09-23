open CoreAndMore
open Lang

module C = FTAConstructor
module A = C.A

module FTAConstructInput = struct
  (* Predicates do not change during execution,
   * so we can safely just treat them all as equal *)
  type predicate = Id.t -> Value.t -> Value.t -> bool
  [@@deriving show]

  let compare_predicate _ _ = 0
  let equal_predicate _ _ = true

  type t =
    {
      context : Context.t ;
      id : Id.t ;
      holes : (Id.t * (Type.t * Type.t * Id.t list)) list ;
      input : Value.t ;
      global_ufform : UFForm.t ;
      predicate : predicate [@ignore] ;
      num_applications : int ;
    }
  [@@deriving eq, hash, ord, show]
end

let construct_empty_fta
    ~(context:Context.t)
    ~(tin:Type.t)
    ~(tout:Type.t)
    ~(id:Id.t)
  : C.t =
  C.initialize_empty
    ~context
    ~id
    ([tin;tout]
     @(List.map ~f:Type.mk_named (Map.keys context.tc))
     @(Map.data context.ec))
    []
    (tin,tout)

let construct_fta_internal
    ~(context:Context.t)
    ~(predicate:Id.t -> Value.t -> Value.t -> bool)
    ~(tin:Type.t)
    ~(tout:Type.t)
    ~(id:Id.t)
    ~(callable_ids:(Id.t * Type.t * Type.t) list)
    (sub_calls:Id.t -> Value.t -> (Value.t * UFForm.t) list)
    (input:Value.t)
    (global_ufform:UFForm.t)
    (num_applications:int)
  : C.t =
  let input_size = Value.size input in
  let ans_o =
    Consts.time
      Consts.initial_creation_times
      (fun _ ->
         let c =
           C.initialize_context
             ~context
             ~value_filter:(fun v_new -> Float.(<=) (Float.of_int (Value.size v_new)) (Float.of_int (input_size) *. 2.))
             ~id
             ([tin;tout]
              @(List.map ~f:Type.mk_named (Map.keys context.tc))
              @(Map.data context.ec)
              @(List.map ~f:(Typecheck.typecheck_value context.ec context.tc context.vc) (Value.subvalues input)))
             [input]
             (tin,tout)
             (fun v1 v2 ->
                predicate id v1 v2 &&
                let form = UFForm.fc id v1 v2 in
                let form = UFForm.band form global_ufform in
                UFForm.satisfiable form)

         in
         let rec get_all_partial_apps
             (ins:Type.t list)
             (base:Expr.t)
             (extractor:Type.t -> Expr.t list)
           : ((Type.t list * Expr.t) list) =
           let basic = (ins,base) in
           let advanced =
             begin match ins with
               | [] -> []
               | h::t ->
                 if Option.is_some (Type.destruct_arr h) then
                   let apps = extractor h in
                   List.concat_map
                     ~f:(fun app ->
                         let base = Expr.mk_app base app in
                         get_all_partial_apps t base extractor)
                     apps
                 else
                   []
             end
           in
           basic::advanced
         in
         let context_conversions =
           List.concat_map
             ~f:(fun (i,_) ->
                 let t = Map.find_exn context.ec i in
                 let (ins,out) = Type.split_to_arg_list_result t in
                 let possible_partials =
                   get_all_partial_apps
                     ins
                     (Expr.mk_var i)
                     (fun t ->
                        List.filter_map
                          ~f:(fun (i,_) ->
                              let t' = Map.find_exn context.ec i in
                              if Typecheck.type_equiv context.tc t t' then
                                (Some (Expr.mk_var i))
                              else
                                None)
                          context.evals)
                 in
                 List.concat_map
                   ~f:(fun (ins,e) ->
                       let ins =
                         List.map
                           ~f:(fun int ->
                               (int
                               ,C.ClassifiedType.TermClassification.Introduction))
                           ins
                       in
                       let e_func = Expr.replace_holes ~i_e:context.evals e in
                       let e_func = Value.to_exp (Eval.evaluate e_func) in
                       let evaluation vs =
                         let es = List.map ~f:Value.to_exp vs in
                         [Eval.evaluate
                            (List.fold
                               ~f:Expr.mk_app
                               ~init:e_func
                               es), UFForm.true_]
                       in
                       [(FTAConstructor.Transition.FunctionApp e
                        ,evaluation
                        ,ins
                        ,(out,C.ClassifiedType.TermClassification.Elimination))
                       ;(FTAConstructor.Transition.FunctionApp e
                        ,evaluation
                        ,ins
                        ,(out,C.ClassifiedType.TermClassification.Introduction))])
                   possible_partials)
             context.evals
         in
         let eval_conversion =
           List.concat_map
             ~f:(fun t ->
                 match Type.node t with
                 | Type.Arrow (t1,t2) ->
                   let evaluate vs =
                     begin match vs with
                       | [f;e] ->
                         let f = Value.to_exp f in
                         let e = Value.to_exp e in
                         [Eval.evaluate (Expr.mk_app f e), UFForm.true_]
                       | _ -> failwith "bad"
                     end
                   in
                   [(FTAConstructor.Transition.Apply
                    ,evaluate
                    ,[(t,C.ClassifiedType.TermClassification.Elimination)
                     ;(t1,C.ClassifiedType.TermClassification.Introduction)]
                    ,(t2,C.ClassifiedType.TermClassification.Elimination))
                   ;(FTAConstructor.Transition.Apply
                    ,evaluate
                    ,[(t,C.ClassifiedType.TermClassification.Elimination)
                     ;(t1,C.ClassifiedType.TermClassification.Introduction)]
                    ,(t2,C.ClassifiedType.TermClassification.Introduction))]
                 | _ -> [])
             (C.get_all_types c)
         in
         let variant_construct_conversions =
           List.concat_map
             ~f:(fun t ->
                 match Type.node t with
                 | Type.Variant l ->
                   List.map
                     ~f:(fun (i,t') ->
                         (FTAConstructor.Transition.VariantConstruct i
                         ,(fun vs -> [Value.mk_ctor i (List.hd_exn vs), UFForm.true_])
                         ,[(t',C.ClassifiedType.TermClassification.Introduction)]
                         ,(t,C.ClassifiedType.TermClassification.Introduction)))
                     l
                 | _ -> [])
             (C.get_all_types c)
         in
         let variant_unsafe_destruct_conversions =
           List.concat_map
             ~f:(fun t ->
                 match Type.node t with
                 | Type.Variant l ->
                   List.concat_map
                     ~f:(fun (i,t') ->
                         [(FTAConstructor.Transition.UnsafeVariantDestruct i,
                           (fun vs ->
                              match Value.destruct_ctor (List.hd_exn vs) with
                              | Some (i',v) ->
                                if Id.equal i i' then [(v,UFForm.true_)] else []
                              | _ -> [])
                          ,[(t,C.ClassifiedType.TermClassification.Elimination)]
                          ,(t',C.ClassifiedType.TermClassification.Elimination))
                         ;(FTAConstructor.Transition.UnsafeVariantDestruct i,
                           (fun vs ->
                              match Value.destruct_ctor (List.hd_exn vs) with
                              | Some (i',v) ->
                                if Id.equal i i' then [(v,UFForm.true_)] else []
                              | _ -> [])
                          ,[(t,C.ClassifiedType.TermClassification.Elimination)]
                          ,(t',C.ClassifiedType.TermClassification.Introduction))])
                     l
                 | _ -> [])
             (C.get_all_types c)
         in
         let tuple_constructors =
           List.filter_map
             ~f:(fun t ->
                 match Type.node t with
                 | Type.Tuple ts ->
                   let ts =
                     List.map
                       ~f:(fun t -> (t,C.ClassifiedType.TermClassification.Introduction))
                       ts
                   in
                   Some (FTAConstructor.Transition.TupleConstruct (List.length ts)
                        ,(fun vs -> [(Value.mk_tuple vs,UFForm.true_)])
                        ,ts
                        ,(t,C.ClassifiedType.TermClassification.Introduction))
                 | _ -> None)
             (C.get_all_types c)
         in
         let tuple_destructors =
           List.concat_map
             ~f:(fun t ->
                 begin match Type.node t with
                   | Type.Tuple ts ->
                     List.concat_mapi
                       ~f:(fun i tout ->
                           [(FTAConstructor.Transition.TupleDestruct (i)
                            ,(fun vs ->
                               [begin match Value.node (List.hd_exn vs) with
                                  | Tuple vs ->
                                    (List.nth_exn vs i,UFForm.true_)
                                  | _ -> failwith "invalid"
                                end])
                            ,[(t,C.ClassifiedType.TermClassification.Elimination)]
                            ,(tout,C.ClassifiedType.TermClassification.Elimination))
                           ;(FTAConstructor.Transition.TupleDestruct i
                            ,(fun vs ->
                               [begin match Value.node (List.hd_exn vs) with
                                  | Tuple vs ->
                                    (List.nth_exn vs i,UFForm.true_)
                                  | _ -> failwith "invalid"
                                end])
                            ,[(t,C.ClassifiedType.TermClassification.Elimination)]
                            ,(tout,C.ClassifiedType.TermClassification.Introduction))])
                       ts
                   | _ -> []
                 end)
             (C.get_all_types c)
         in
         let angelic_call_conversions =
           let evaluation i vs =
             begin match vs with
               | [v1] ->
                 let break = fun v ->
                   let t =
                     Typecheck.typecheck_value
                       context.ec
                       context.tc
                       context.vc
                       v
                   in
                   C.is_recursive_type
                     c
                     t
                 in
                 if Value.strict_functional_subvalue ~break v1 input then
                   begin
                     (*print_endline (Value.show v1);
                       print_endline (string_of_list Value.show (sub_calls v1));*)
                     sub_calls i v1
                   end
                 else
                   []
                 (*if Value.size v1 < Value.size input then
                   begin
                     sub_calls i v1
                   end
                 else
                   []*)
               | _ -> failwith "invalid"
             end
           in
           List.concat_map
             ~f:(fun (id,tin,tout) ->
                 [(FTAConstructor.Transition.AngelicCall id
                  ,evaluation id
                  ,[(tin,C.ClassifiedType.TermClassification.Introduction)]
                  ,(tout,C.ClassifiedType.TermClassification.Elimination))
                 ;(FTAConstructor.Transition.AngelicCall id
                  ,evaluation id
                  ,[(tin,C.ClassifiedType.TermClassification.Introduction)]
                  ,(tout,C.ClassifiedType.TermClassification.Introduction))])
             callable_ids
         in
         let conversions =
           variant_construct_conversions
           @ tuple_constructors
           @ eval_conversion
           @ tuple_destructors
           @ variant_unsafe_destruct_conversions
         in
         let all_conversions =
           context_conversions
           @ angelic_call_conversions
           @ conversions
         in
         let _ =
           List.fold
             ~f:(fun last_adds i ->
                 begin match last_adds with
                   | None -> None
                   | Some (old_added,old_pruned) ->
                     let (d1,e1) = C.update_from_conversions c variant_unsafe_destruct_conversions in
                     let (d2,e2) = C.update_from_conversions c tuple_destructors in
                     let (d3,e3) =
                       C.update_from_conversions c conversions
                     in
                     let (d4,_) =
                       C.update_from_conversions c all_conversions
                     in
                     let new_added = (List.length d1) + (List.length d2) + (List.length d3) + (List.length d4) in
                     let new_pruned = (List.length e1) + (List.length e2) + (List.length e3) + (List.length d4) in
                     if new_pruned > 0 &&
                        (new_added = 0 ||
                         (Float.to_int (Float.of_int new_added *. 5.0) < old_added && new_pruned > (Float.to_int (Float.of_int old_pruned *. 5.0)))) then
                       None
                     else
                       Some (new_added, new_pruned)
                 end)
             ~init:(Some (0,0))
             (range 0 num_applications)
         in
         begin
           (* Ok, so we're at a global minima in terms of efficiency here

              Essentially, for efficiency, I have removed the destructors.
              However, I then must also remove the minimization procedure, as
              otherwise top removed during minimization. I strongly believe this
              is better than adding in the destructors right here, but I also
              believe there is a more efficient strategy: simply do not remove
              top during minimization. However, I'm too lazy to do that right
              now, so this is a TODO -- make top not removed during minimization
              and then add back in the C.minimize (keep not having the
              destructors, though).
           *)
           (*C.add_destructors c;*)
           (*let c = C.minimize c in*)
           c
         end)
  in
  ans_o

let construct_fta_unfolded
    (rec_call:FTAConstructInput.t -> C.t)
    (instruct:FTAConstructInput.t)
  : C.t =
  let holes = instruct.holes in
  let id = instruct.id in
  let context = instruct.context in
  let num_applications = instruct.num_applications in
  let find_info_of_call i =
    List.Assoc.find_exn ~equal:Id.equal holes i
  in
  let (tin,tout,calls) = find_info_of_call id in
  let callable_ids =
    List.map
      ~f:(fun id ->
          let (tin,tout,_) = find_info_of_call id in
          (id,tin,tout))
      calls
  in
  let global_ufform = instruct.global_ufform in
  let predicate = instruct.predicate in
  let sub_calls id input =
    let rec_input : FTAConstructInput.t =
      {
        context  ;
        id ;
        holes  ;
        input ;
        global_ufform  ;
        num_applications  ;
        predicate ;
      }
    in
    let c = rec_call rec_input in
    let v = C.get_final_values c input in
    v
  in
  let c = construct_fta_internal
    ~context
    ~predicate
    ~tin
    ~tout
    ~id
    ~callable_ids
    sub_calls
    instruct.input
    global_ufform
    num_applications
    in
    c

module M =
  FixMemoizerOf(
  struct
    module Arg = FTAConstructInput

    module Result = C

    let f = construct_fta_unfolded
  end)

let construct_fta
    ~(context:Context.t)
    ~(predicate:Id.t -> Value.t -> Value.t -> bool)
    ~(holes:(Id.t * (Type.t * Type.t * Id.t list)) list)
    (id:Id.t)
    (input:Value.t)
    (num_applications:int)
    (global_ufform:UFForm.t)
  : C.t =
  let rec_input : FTAConstructInput.t =
    {
      context  ;
      id ;
      holes  ;
      input ;
      global_ufform  ;
      predicate ;
      num_applications  ;
    }
  in
  M.v rec_input

let get_finals
    ~(context:Context.t)
    ~(predicate:Id.t -> Value.t -> Value.t -> bool)
    ~(holes:(Id.t * (Type.t * Type.t * Id.t list)) list)
    (id:Id.t)
    (input:Value.t)
    (num_applications:int)
    (global_ufform:UFForm.t)
  : (Value.t * UFForm.t) list =
  let c =
    construct_fta
      ~context
      ~predicate
      ~holes
      id
      input
      num_applications
      global_ufform
  in
  let ans = C.get_final_values c input in
  ans



