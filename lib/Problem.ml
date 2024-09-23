open CoreAndMore
open Lang

open Typecheck

type synth_target = Id.t * (Type.t * Type.t * (Id.t list))
[@@deriving eq, hash, ord, show]

type t_unprocessed = string list
                     * Declaration.t list
                     * synth_target list
                     * Declaration.t list
                     * Spec.t list
[@@deriving show]

let update_import_base
    (ss:string list)
    (fname:string)
  : string list =
  let dir = Filename.dirname fname in
  List.map ~f:((^) (dir ^ "/")) ss

let update_all_import_bases
    ((ss,ds,t,dss,ios):t_unprocessed)
    (fname:string)
  : t_unprocessed =
  let ss = update_import_base ss fname in
  (ss,ds,t,dss,ios)

let extract_file
    ((ss,ds,t,dss,ios):t_unprocessed)
  : (string * t_unprocessed) option =
  begin match split_by_last ss with
    | None -> None
    | Some (ss,h) -> Some (h,(ss,ds,t,dss,ios))
  end

let merge_unprocessed
    ((ss,ds,t,dss,ios):t_unprocessed)
    ((imports,decls):string list * Declaration.t list)
  : t_unprocessed =
  (imports@ss,decls@ds,t,dss,ios)

type t = {
  synth_targets : synth_target list        ;
  ec           : Context.Exprs.t          ;
  tc           : Context.Types.t          ;
  vc           : Context.Variants.t       ;
  specs     : Spec.t list ;
  i     : (Value.t * Value.t) list ;
  eval_context : (Id.t * Expr.t) list     ;
  unprocessed  : t_unprocessed            ;
  full_ec           : Context.Exprs.t          ;
  full_tc           : Context.Types.t          ;
  full_vc           : Context.Variants.t       ;
  full_eval_context : (Id.t * Expr.t) list     ;
}
[@@deriving make]


let dummy_of_context
    (c:Context.t)
  : t =
  {
    synth_targets = [] ;
    ec = c.ec ;
    tc = c.tc ;
    vc = c.vc ;
    specs = [Test ([],Expr.mk_true_exp)] ;
    i = [] ;
    eval_context = c.evals ;
    unprocessed = ([],[],[],[],[Test ([],Expr.mk_true_exp)]) ;
    full_ec = c.full_ec ;
    full_tc = c.full_tc ;
    full_vc = c.full_vc ;
    full_eval_context = c.full_evals ;
  }


let extract_variants
    (t:Type.t)
    : (Context.Variants.key * Context.Variants.value) list =
  fst
    (Type.fold
       ~name_f:(fun i -> ([],Type.mk_named i))
       ~arr_f:(fun (vs1,t1) (vs2,t2) -> (vs1@vs2,Type.mk_arrow t1 t2))
       ~tuple_f:(fun vss_ts ->
           let (vss,ts) = List.unzip vss_ts in
           (List.concat vss, Type.mk_tuple ts))
       ~mu_f:(fun _ vs -> vs)
       ~variant_f:(fun ids_vss_ts ->
           let (ids,vss_ts) = List.unzip ids_vss_ts in
           let (vss,ts) = List.unzip vss_ts in
           let ids_ts = List.zip_exn ids ts in
           let ids_map = List.map ~f:(fun id -> (id,ids_ts)) ids in
           (ids_map@(List.concat vss), Type.mk_variant ids_ts))
       ~universal_f:(fun id ->
         ([],Type.mk_universal id))
       t)

let process_decl_list
    (ec:Context.Exprs.t)
    (tc:Context.Types.t)
    (vc:Context.Variants.t)
    (i_e:(Id.t * Expr.t) list)
    (ds:Declaration.t list)
  : (Context.Exprs.t * Context.Types.t * Context.Variants.t * (Id.t * Expr.t) list)
    * (Context.Exprs.t * Context.Types.t * Context.Variants.t * (Id.t * Expr.t) list) =
    (List.fold_left
       ~f:(fun ((new_ec,new_tc,new_vc,new_i_e),(ec,tc,vc,i_e)) decl ->
           Declaration.fold
             ~type_f:(fun i t ->
                 let all_variants = extract_variants t in
                 ((new_ec
                  ,Map.set new_tc ~key:i ~data:t
                  ,List.fold_left
                      ~f:(fun vc (k,v) -> Map.set vc ~key:k ~data:v)
                      ~init:new_vc
                      all_variants
                  ,new_i_e)
                 ,(ec
                  ,Map.set tc ~key:i ~data:t
                  ,List.fold_left
                      ~f:(fun vc (k,v) -> Map.set vc ~key:k ~data:v)
                      ~init:vc
                      all_variants
                  ,i_e))
               )
             ~expr_f:(fun i e ->
                 let t = typecheck_exp ec tc vc e in
                 ((Map.set new_ec ~key:i ~data:t
                  ,new_tc
                  ,new_vc
                  ,(i,e)::new_i_e)
                 ,(Map.set ec ~key:i ~data:t
                  ,tc
                  ,vc
                  ,(i,e)::i_e))
               )
             decl)
       ~init:(((Context.empty,Context.empty,Context.empty,[])
              ,(ec,tc,vc,i_e)))
       ds)

let st_to_pair
    (synth_type:Type.t)
  : Type.t * Type.t =
  fold_until_completion
    ~f:(fun (acc,t) ->
        begin match Type.node t with
          | Type.Arrow (t1,t2) -> Left (t1::acc,t2)
          | _ -> Right (Type.mk_tuple (List.rev acc),t)
        end)
    ([],synth_type)

let process_spec
    (ec:Context.Exprs.t)
    (tc:Context.Types.t)
    (vc:Context.Variants.t)
    (i_e:(Id.t * Expr.t) list)
    (synth_targets:synth_target list)
    (ss:Spec.t) : unit =
  begin match ss with
    | IO (i,ein,eout) ->
      let typecheck = Typecheck.typecheck_exp ec tc vc in
      let e_tin = typecheck ein in
      let e_tout = typecheck eout in
      let ex_t = Type.mk_arrow e_tin e_tout in
      let (synth_in,synth_out,_) = List.Assoc.find_exn ~equal:Id.equal synth_targets i in
      let synth_type = Type.mk_arrow synth_in synth_out in
      if Typecheck.type_equiv tc synth_type ex_t then
        ()
      else
        failwith "example doesn't satisfy the expected type"
    | Post (i,e) ->
      let (synth_in,synth_out,_) = List.Assoc.find_exn ~equal:Id.equal synth_targets i in
      let expected_pred_type =
        Type.mk_arrow
          synth_in
          (Type.mk_arrow synth_out Type._bool)
      in
      let pred_type = Typecheck.typecheck_exp ec tc vc e in
      if Typecheck.type_equiv tc expected_pred_type pred_type then
        ()
      else
        failwith "example doesn't satisfy the expected type"
    | Test uf ->
      let t =
        Typecheck.typecheck_exp
          (Context.set_multiple ec (fst uf))
          tc
          vc
          (snd uf)
      in
      assert
        (Typecheck.type_equiv
           tc
           t
           Type._bool)
    | Equiv (i,e) ->
      let t =
        Typecheck.typecheck_exp
          ec
          tc
          vc
          e
      in
      let (synth_in,synth_out,_) = List.Assoc.find_exn ~equal:Id.equal synth_targets i in
      if Typecheck.type_equiv tc t (Type.mk_arrow synth_in synth_out) then
        ()
      else
        failwith "equivalence check doesn't satisfy the expected type"
  end

let process_specs
    (ec:Context.Exprs.t)
    (tc:Context.Types.t)
    (vc:Context.Variants.t)
    (i_e:(Id.t * Expr.t) list)
    (synth_targets:synth_target list)
    (ss:Spec.t list) : unit =
  let ec =
    Context.set_multiple
      ec
      (List.map
         ~f:(fun (i,(tin,tout,_)) ->
             (i, Type.mk_arrow tin tout))
         synth_targets)
  in
  List.iter
    ~f:(process_spec ec tc vc i_e synth_targets)
    ss

let process (unprocessed : t_unprocessed) : t =
  let (_,decs,synth_targets,dss,uspec) = unprocessed in
  let (ec,tc,vc,eval_context) =
    fst
      (process_decl_list
         Context.empty
         Context.empty
         Context.empty
         []
         decs)
  in
  (*let st = synth_targets in*)
  let (full_ec,full_tc,full_vc,full_eval_context) =
    snd
      (process_decl_list
         ec
         tc
         vc
         eval_context
         dss)
  in
  process_specs full_ec full_tc full_vc full_eval_context synth_targets uspec;
  make
    ~ec
    ~tc
    ~vc
    ~eval_context
    ~unprocessed
    ~synth_targets
    ~specs:uspec
    ~full_ec
    ~full_tc
    ~full_vc
    ~full_eval_context
    ()

let extract_context
    (p:t)
  : Context.t =
  {
    ec = p.ec ;
    tc = p.tc ;
    vc = p.vc ;
    full_ec = p.full_ec ;
    full_tc = p.full_tc ;
    full_vc = p.full_vc ;
    evals = p.eval_context ;
    full_evals = p.full_eval_context ;
  }
