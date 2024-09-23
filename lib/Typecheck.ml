open CoreAndMore
open Lang

let type_equiv
    (tc:Context.Types.t)
    (t1:Type.t)
    (t2:Type.t)
  : bool =
  let rec type_equiv_internal
      (tc1:Context.Types.t)
      (tc2:Context.Types.t)
      (t1:Type.t)
      (t2:Type.t)
    : bool =
    let replace_with_definition
        (tc:Context.Types.t)
        (v:Id.t)
      : Type.t =
      Map.find_exn tc v
    in
    let type_equiv_simple = type_equiv_internal tc1 tc2 in
    begin match (Type.node t1,Type.node t2) with
      | (Named i1, Named i2) ->
        if Id.equal i1 i2 then
          true
        else
          let t1 = replace_with_definition tc1 i1 in
          let t2 = replace_with_definition tc2 i2 in
          type_equiv_simple t1 t2
      | (Named i1, _) ->
        let t1 = replace_with_definition tc1 i1 in
        type_equiv_simple t1 t2
      | (_, Named i2) ->
        let t2 = replace_with_definition tc2 i2 in
        type_equiv_simple t1 t2
      | (Mu _, Mu _) ->
        Type.equal t1 t2
      | (Mu (i1,t1'), _) ->
        let tc1 = Map.set tc1 ~key:i1 ~data:t1 in
        type_equiv_internal tc1 tc2 t1' t2
      | (_, Mu (i2,t2')) ->
        let tc2 = Map.set tc2 ~key:i2 ~data:t2 in
        type_equiv_internal tc1 tc2 t1 t2'
      | (Arrow (t11,t12), Arrow (t21,t22)) ->
        let t1_equiv = type_equiv_simple t11 t21 in
        let t2_equiv = type_equiv_simple t12 t22 in
        t1_equiv && t2_equiv
      | (Arrow _, _) -> false
      | (_, Arrow _) -> false
      | (Tuple t1s, Tuple t2s) ->
        Option.value_map
          ~default:false
          ~f:(fun t1t2s ->
              List.fold_left
                ~f:(fun acc_b (t1,t2) ->
                    acc_b && type_equiv_simple t1 t2)
                ~init:true
                t1t2s)
          (or_unequal_lengths_to_option (List.zip t1s t2s))
      | (Tuple _, _) -> false
      | (_, Tuple _) -> false
      | (Variant idts1, Variant idts2) ->
        Option.value_map
          ~default:false
          ~f:(fun t1t2s ->
              List.fold_left
                ~f:(fun acc_b ((id1,t1),(id2,t2)) ->
                    acc_b
                    && type_equiv_simple t1 t2
                    && Id.equal id1 id2)
                ~init:(true)
                t1t2s)
          (or_unequal_lengths_to_option (List.zip idts1 idts2))
      | (Universal i1, Universal i2) ->
        Id.equal i1 i2
      | (Universal _, _) | (_, Universal _) -> false
    end
  in
  type_equiv_internal tc tc t1 t2

let rec concretify
    (tc:Context.Types.t)
    (t:Type.t)
  : Type.t =
  begin match Type.node t with
    | Named i ->
      concretify tc (Map.find_exn tc i)
    | Mu (i, t') ->
      let tc = Map.set tc ~key:i ~data:t in
      concretify tc t'
    | _ -> t
  end

let rec typecheck_pattern
    (tc:Context.Types.t)
    (p:Pattern.t)
    (t:Type.t)
  : (Id.t * Type.t) list =
  begin match (p,Type.node (concretify tc t)) with
    | (Tuple ps, Tuple ts) ->
      let merges =
        List.map2_exn
          ~f:(typecheck_pattern tc)
          ps
          ts
      in
      List.concat merges
    | (Ctor (i,p),Variant variants) ->
      let t = List.Assoc.find_exn ~equal:Id.equal variants i in
      typecheck_pattern tc p t
    | (Var i,_) -> [(i,t)]
    | (Wildcard,_) -> []
    | _ -> failwith ("didn't merge " ^ (Pattern.show p) ^ " with " ^ (Type.show t))
  end

let rec typecheck_exp
    (ec:Context.Exprs.t)
    (tc:Context.Types.t)
    (vc:Context.Variants.t)
    (e:Expr.t)
  : Type.t =
  let typecheck_simple = typecheck_exp ec tc vc in
  begin match Expr.node e with
    | Unctor _ -> failwith "not typeable"
    | Var v ->
      begin match Map.find ec v with
        | None -> failwith ("variable " ^ (Id.show v) ^ " not found")
        | Some e -> e
      end
    | Eq (_,e1,e2) ->
      let t1 = typecheck_simple e1 in
      let t2 = typecheck_simple e2 in
      if (type_equiv tc t1 t2) then
        Type._bool
      else
        failwith ((Type.show t1) ^ " is not equivalent to " ^ (Type.show t2))
    | LTE (e1,e2) ->
      let t1 = typecheck_simple e1 in
      let t2 = typecheck_simple e2 in
      if (type_equiv tc t1 t2) then
        Type._bool
      else
        failwith ((Type.show t1) ^ " is not equivalent to " ^ (Type.show t2))
    | App (e1,e2) ->
      let t1 = concretify tc (typecheck_simple e1) in
      let (t11,t12) = Type.destruct_arr_exn t1 in
      let t2 = typecheck_simple e2 in
      if type_equiv tc t11 t2 then
        t12
      else
        failwith ("applied invalid type: "
                  ^ (Type.show t2)
                  ^ " instead of "
                  ^ (Type.show t11))
    | Func ((i,t),e) ->
      let ec = Map.set ec ~key:i ~data:t in
       Type.mk_arrow t (typecheck_exp ec tc vc e)
    | Ctor (i,e) ->
      let t = typecheck_simple e in
      let its = Map.find_exn vc i in
      let t_defined =
        List.Assoc.find_exn ~equal:Id.equal its i
      in
      if type_equiv tc t_defined t then
        Type.mk_variant its
      else
        failwith ("variant " ^ (Id.show i) ^ " expects different type: expected "
                  ^ (Type.show t_defined) ^ " but got " ^ (Type.show t))
    | Match(e,branches) ->
      let t = concretify tc (typecheck_simple e) in
      let ts =
        List.map
          ~f:(fun (p,e) ->
              let its = typecheck_pattern tc p t in
              let ec = Context.set_multiple ec its in
              typecheck_exp ec tc vc e)
          branches
      in
      let (ht,tt) = split_by_first_exn ts in
      List.iter
        ~f:(fun t ->
            if not (type_equiv tc ht t) then
              failwith ("type not equiv" ^ (Type.show ht) ^ (Type.show t))
            else
              ())
        tt;
      ht
    | Fix (i,t,e) ->
      let ec = Map.set ec ~key:i ~data:t in
      typecheck_exp ec tc vc e
    | Tuple es ->
      Type.mk_tuple
        (List.map
           ~f:typecheck_simple
           es)
    | Proj (i,e) ->
      let t = concretify tc (typecheck_simple e) in
      let ts = Type.destruct_tuple_exn t in
      List.nth_exn ts i
    | Abstract (i,_) ->
      Type.mk_universal i
  end

let rec align_types
    (t:Type.t)
    (e:Expr.t)
  : Expr.t =
  begin match (Type.node t,Expr.node e) with
    | (_, Fix (i,_,e)) ->
      Expr.mk_fix i t (align_types t e)
    | (Type.Arrow (t1,t2), Func ((i,_),e)) ->
      Expr.mk_func (i,t1) (align_types t2 e)
    | _ -> e
  end

let all_subtypes
    (tc:Context.Types.t)
    (t:Type.t)
  : Type.t list =
  let rec all_subtypes
      (t:Type.t)
      (added:Type.t list)
    : Type.t list =
    if List.mem ~equal:Type.equal added t then
      added
    else
      let added = t::added in
      begin match Type.node t with
        | Named i ->
          all_subtypes
            (Map.find_exn tc i)
            added
        | Arrow (t1,t2) ->
          let added =
            all_subtypes
              t1
              added
          in
          all_subtypes
            t2
            added
        | Tuple ts ->
          List.fold
            ~f:(fun added t ->
                all_subtypes
                  t
                  added)
            ~init:added
            ts
        | Mu (i,t') ->
          let t = Type.replace t' i t in
          all_subtypes
            t
            added
        | Variant branches ->
          List.fold
            ~f:(fun added (_,t) ->
                all_subtypes
                  t
                  added)
            ~init:added
            branches
        | Universal _ -> added
      end
  in
  all_subtypes
    t
    []

let rec typecheck_value
    (ec:Context.Exprs.t)
    (tc:Context.Types.t)
    (vc:Context.Variants.t)
    (v:Value.t)
  : Type.t =
  let typecheck_simple = typecheck_value ec tc vc in
  begin match Value.node v with
    | Ctor (i,e) ->
      let t = typecheck_simple e in
      let its = Map.find_exn vc i in
      let t_defined =
        List.Assoc.find_exn ~equal:Id.equal its i
      in
      if type_equiv tc t_defined t then
        Type.mk_variant its
      else
        failwith ("variant " ^ (Id.show i) ^ " expects different type: expected "
                  ^ (Type.show t_defined) ^ " but got " ^ (Type.show t))
    | Tuple es ->
      Type.mk_tuple
        (List.map
           ~f:typecheck_simple
           es)
    | Func ((i,t),e) ->
      let ec = Map.set ec ~key:i ~data:t
      in Type.mk_arrow t (typecheck_exp ec tc vc e)
    | Abstract (id,_) ->
      Type.mk_universal id
  end

let rec is_singleton
    (tc:Context.Types.t)
    (t:Type.t)
  : bool =
  begin match Type.node t with
    | Named i ->
      begin match Map.find tc i with
        | None -> true
        | Some t -> is_singleton tc t
      end
    | Tuple ts ->
      List.for_all ~f:(is_singleton tc) ts
    | Arrow _ -> false (*not technically correct*)
    | Mu (_,t) -> is_singleton tc t
    | Variant _ -> false (*not technically correct*)
    | Universal _ -> false
  end

let rec extract_singleton
    (tc:Context.Types.t)
    (t:Type.t)
  : Value.t =
  begin match Type.node t with
    | Named i ->
      extract_singleton tc (Map.find_exn tc i)
    | Tuple ts ->
      Value.mk_tuple
        (List.map ~f:(extract_singleton tc) ts)
    | Arrow _ -> failwith "ah"
    | Mu (_,t) -> extract_singleton tc t
    | Variant _ -> failwith "ah"
    | Universal _ -> failwith "ah"
  end

let rec extract_value
    (c:Context.t)
    (t:Type.t)
  : Value.t option =
    begin match Type.node t with
      | Named i ->
        Option.(>>=)
          (Map.find c.tc i)
          (fun t -> extract_value c t)
      | Arrow (_,_) -> failwith "not address hofs here"
      | Tuple ts ->
        let eso = List.map ~f:(extract_value c) ts in
        begin match distribute_option eso with
          | None -> None
          | Some es -> Some (Value.mk_tuple es)
        end
      | Mu (_,t) ->
        extract_value c t
      | Variant branches ->
        List.fold
          ~f:(fun acco (i,t) ->
              begin match acco with
                | None ->
                  let vo = extract_value c t in
                  Option.map
                    ~f:(fun v -> Value.mk_ctor i v)
                    vo
                | Some e -> Some e
              end)
          ~init:None
          branches
      | Universal id -> Some (Value.mk_abstract id 0)
    end

let extract_value_exn
    (c:Context.t)
    (t:Type.t)
  : Value.t =
  Option.value_exn (extract_value c t)
