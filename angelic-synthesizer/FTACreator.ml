open CoreAndMore
open Contata.Lang

module A = TimbukSimple.Automaton.Make(FTAConstructor.Transition)(FTAConstructor.State)(FTAConstructor.Reqs)

module C = FTAConstructor.Make(A)(FTAConstructor.ExtractorSingleton)

module FTAConstructInput = struct
  type t =
    {
      context : Contata.Context.t ;
      id : Id.t ;
      holes : (Id.t * (Contata.Type.t * Contata.Type.t * Id.t list)) list ;
      input : Value.t ;
      global_ufform : Contata.UFForm.t ;
      num_applications : int ;
    }
  [@@deriving eq, hash, ord, show]
end

let construct_fta_internal
    ~(context:Contata.Context.t)
    ~(tin:Contata.Type.t)
    ~(tout:Contata.Type.t)
    ~(id:Id.t)
    ~(callable_ids:(Id.t * Contata.Type.t * Contata.Type.t) list)
    (sub_calls:Id.t -> Value.t -> Value.t list)
    (input:Value.t)
    (global_ufform:Contata.UFForm.t)
    (num_applications:int)
  : C.t =
  let ans_o =
    Contata.Consts.time
      Contata.Consts.initial_creation_times
      (fun _ ->
         let c =
           C.initialize_context
             ~context
             ~value_filter:(func_of true)
             ([tin;tout]
              @(List.map ~f:Contata.Type.mk_named (Map.keys context.tc))
              @(Map.data context.ec)
              @(List.map ~f:(Contata.Typecheck.typecheck_value context.ec context.tc context.vc) (Value.subvalues input)))
             [input]
             (tin,tout)
             (fun v1 v2 ->
                let form = Contata.UFForm.fc id v1 v2 in
                let form = Contata.UFForm.band form global_ufform in
                Contata.UFForm.satisfiable form)

         in
         let rec get_all_partial_apps
             (ins:Contata.Type.t list)
             (base:Expr.t)
             (extractor:Contata.Type.t -> Expr.t list)
           : ((Contata.Type.t list * Expr.t) list) =
           let basic = (ins,base) in
           let advanced =
             begin match ins with
               | [] -> []
               | h::t ->
                 if Option.is_some (Contata.Type.destruct_arr h) then
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
                 let (ins,out) = Contata.Type.split_to_arg_list_result t in
                 let possible_partials =
                   get_all_partial_apps
                     ins
                     (Expr.mk_var i)
                     (fun t ->
                        List.filter_map
                          ~f:(fun (i,_) ->
                              let t' = Map.find_exn context.ec i in
                              if Contata.Typecheck.type_equiv context.tc t t' then
                                (Some (Expr.mk_var i))
                              else
                                None)
                          context.evals)
                 in
                 List.concat_map
                   ~f:(fun (ins,e) ->
                       let ins =
                         List.map
                           ~f:(fun int -> (int,Contata.FTAConstructor.ClassifiedType.TermClassification.Introduction))
                           ins
                       in
                       let e_func = Expr.replace_holes ~i_e:context.evals e in
                       let e_func = Value.to_exp (Contata.Eval.evaluate e_func) in
                       let evaluation vs =
                         let es = List.map ~f:Value.to_exp vs in
                         [Contata.Eval.evaluate
                            (List.fold
                               ~f:Expr.mk_app
                               ~init:e_func
                               es)]
                       in
                       [(FTAConstructor.Transition.FunctionApp e,evaluation,ins,(out,Contata.FTAConstructor.ClassifiedType.TermClassification.Elimination))
                       ;(FTAConstructor.Transition.FunctionApp e,evaluation,ins,(out,Contata.FTAConstructor.ClassifiedType.TermClassification.Introduction))])
                   possible_partials)
             context.evals
         in
         let eval_conversion =
           List.concat_map
             ~f:(fun t ->
                 match Contata.Type.node t with
                 | Contata.Type.Arrow (t1,t2) ->
                   let evaluate vs =
                     begin match vs with
                       | [f;e] ->
                         let f = Value.to_exp f in
                         let e = Value.to_exp e in
                         [Contata.Eval.evaluate (Expr.mk_app f e)]
                       | _ -> failwith "bad"
                     end
                   in
                   [(FTAConstructor.Transition.Apply
                    ,evaluate
                    ,[(t,Contata.FTAConstructor.ClassifiedType.TermClassification.Elimination)
                     ;(t1,Contata.FTAConstructor.ClassifiedType.TermClassification.Introduction)]
                    ,(t2,Contata.FTAConstructor.ClassifiedType.TermClassification.Elimination))
                   ;(FTAConstructor.Transition.Apply
                    ,evaluate
                    ,[(t,Contata.FTAConstructor.ClassifiedType.TermClassification.Elimination)
                     ;(t1,Contata.FTAConstructor.ClassifiedType.TermClassification.Introduction)]
                    ,(t2,Contata.FTAConstructor.ClassifiedType.TermClassification.Introduction))]
                 | _ -> [])
             (C.get_all_types c)
         in
         let variant_construct_conversions =
           List.concat_map
             ~f:(fun t ->
                 match Contata.Type.node t with
                 | Contata.Type.Variant l ->
                   List.map
                     ~f:(fun (i,t') ->
                         (FTAConstructor.Transition.VariantConstruct i
                         ,(fun vs -> [Value.mk_ctor i (List.hd_exn vs)])
                         ,[(t',Contata.FTAConstructor.ClassifiedType.TermClassification.Introduction)]
                         ,(t,Contata.FTAConstructor.ClassifiedType.TermClassification.Introduction)))
                     l
                 | _ -> [])
             (C.get_all_types c)
         in
         let variant_unsafe_destruct_conversions =
           List.concat_map
             ~f:(fun t ->
                 match Contata.Type.node t with
                 | Contata.Type.Variant l ->
                   List.concat_map
                     ~f:(fun (i,t') ->
                         [(FTAConstructor.Transition.UnsafeVariantDestruct i,
                           (fun vs ->
                              match Value.destruct_ctor (List.hd_exn vs) with
                              | Some (i',v) ->
                                if Id.equal i i' then [v] else []
                              | _ -> [])
                          ,[(t,Contata.FTAConstructor.ClassifiedType.TermClassification.Elimination)]
                          ,(t',Contata.FTAConstructor.ClassifiedType.TermClassification.Elimination))
                         ;(FTAConstructor.Transition.UnsafeVariantDestruct i,
                           (fun vs ->
                              match Value.destruct_ctor (List.hd_exn vs) with
                              | Some (i',v) ->
                                if Id.equal i i' then [v] else []
                              | _ -> [])
                          ,[(t,Contata.FTAConstructor.ClassifiedType.TermClassification.Elimination)]
                          ,(t',Contata.FTAConstructor.ClassifiedType.TermClassification.Introduction))])
                     l
                 | _ -> [])
             (C.get_all_types c)
         in
         let tuple_constructors =
           List.filter_map
             ~f:(fun t ->
                 match Contata.Type.node t with
                 | Contata.Type.Tuple ts ->
                   let ts =
                     List.map
                       ~f:(fun t -> (t,Contata.FTAConstructor.ClassifiedType.TermClassification.Introduction))
                       ts
                   in
                   Some (FTAConstructor.Transition.TupleConstruct (List.length ts)
                        ,(fun vs -> [Value.mk_tuple vs])
                        ,ts
                        ,(t,Contata.FTAConstructor.ClassifiedType.TermClassification.Introduction))
                 | _ -> None)
             (C.get_all_types c)
         in
         let tuple_destructors =
           List.concat_map
             ~f:(fun t ->
                 begin match Contata.Type.node t with
                   | Contata.Type.Tuple ts ->
                     List.concat_mapi
                       ~f:(fun i tout ->
                           [(FTAConstructor.Transition.TupleDestruct (i)
                            ,(fun vs ->
                               [begin match Value.node (List.hd_exn vs) with
                                  | Tuple vs ->
                                    List.nth_exn vs i
                                  | _ -> failwith "invalid"
                                end])
                            ,[(t,Contata.FTAConstructor.ClassifiedType.TermClassification.Elimination)]
                            ,(tout,Contata.FTAConstructor.ClassifiedType.TermClassification.Elimination))
                           ;(FTAConstructor.Transition.TupleDestruct i
                            ,(fun vs ->
                               [begin match Value.node (List.hd_exn vs) with
                                  | Tuple vs ->
                                    List.nth_exn vs i
                                  | _ -> failwith "invalid"
                                end])
                            ,[(t,Contata.FTAConstructor.ClassifiedType.TermClassification.Elimination)]
                            ,(tout,Contata.FTAConstructor.ClassifiedType.TermClassification.Introduction))])
                       ts
                   | _ -> []
                 end)
             (C.get_all_types c)
         in
         let angelic_call_conversions =
           let evaluation i vs =
             begin match vs with
               | [v1] ->
                 if Value.size v1 < Value.size input then
                   begin
                     sub_calls i v1
                   end
                 else
                   []
               | _ -> failwith "invalid"
             end
           in
           List.concat_map
             ~f:(fun (id,tin,tout) ->
                 [(FTAConstructor.Transition.AngelicCall id
                  ,evaluation id
                  ,[(tin,Contata.FTAConstructor.ClassifiedType.TermClassification.Introduction)]
                  ,(tout,Contata.FTAConstructor.ClassifiedType.TermClassification.Elimination))
                 ;(FTAConstructor.Transition.AngelicCall id
                  ,evaluation id
                  ,[(tin,Contata.FTAConstructor.ClassifiedType.TermClassification.Introduction)]
                  ,(tout,Contata.FTAConstructor.ClassifiedType.TermClassification.Introduction))])
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
             ~f:(fun last_adds _ ->
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
  let sub_calls id input =
    let rec_input : FTAConstructInput.t =
      {
        context  ;
        id ;
        holes  ;
        input ;
        global_ufform  ;
        num_applications  ;
      }
    in
    let c = rec_call rec_input in
    C.get_final_values c input
  in
  construct_fta_internal
    ~context
    ~tin
    ~tout
    ~id
    ~callable_ids
    sub_calls
    instruct.input
    global_ufform
    num_applications

module M =
  FixMemoizerOf(
  struct
    module Arg = FTAConstructInput

    module Result = C

    let f = construct_fta_unfolded
  end)

let construct_fta
    ~(context:Contata.Context.t)
    ~(holes:(Id.t * (Contata.Type.t * Contata.Type.t * Id.t list)) list)
    (id:Id.t)
    (input:Value.t)
    (num_applications:int)
    (global_ufform:Contata.UFForm.t)
  : C.t =
  let rec_input : FTAConstructInput.t =
    {
      context  ;
      id ;
      holes  ;
      input ;
      global_ufform  ;
      num_applications  ;
    }
  in
  M.v rec_input

let get_finals
    ~(context:Contata.Context.t)
    ~(holes:(Id.t * (Contata.Type.t * Contata.Type.t * Id.t list)) list)
    (id:Id.t)
    (input:Value.t)
    (num_applications:int)
    (global_ufform:Contata.UFForm.t)
  : Value.t list =
  let c =
    construct_fta
      ~context
      ~holes
      id
      input
      num_applications
      global_ufform
  in
  C.get_final_values c input
