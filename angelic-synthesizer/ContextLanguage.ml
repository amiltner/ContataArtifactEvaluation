open CoreAndMore
open Contata

module Expr = struct
  type t =
    | Var of Id.t
    | App of t * t
    | Func of Param.t * t
    | Ctor of Id.t * t
    | Unctor of Id.t * t
    | Eq of bool * t * t
    | Match of t * (Lang.Pattern.t * t) list
    | Fix  of Id.t * Type.t * t
    | Tuple of t list
    | Proj of int * t
    | Abstract of Id.t * int
    | LTE of t * t
  [@@deriving eq, hash, ord, show]

  let rec replace
      (i:Id.t)
      (e_with:t)
      (e:t)
    : t =
    let replace_simple = replace i e_with in
    begin match e with
      | Eq (b,e1,e2) ->
        Eq (b,(replace_simple e1),(replace_simple e2))
      | Var i' ->
        if Id.equal i i' then
          e_with
        else
          e
      | App (e1,e2) ->
        App ((replace_simple e1),(replace_simple e2))
      | Func ((i',t),e') ->
        if Id.equal i i' then
          e
        else
          Func ((i',t),(replace_simple e'))
      | Ctor (i,e) ->
        Ctor (i,(replace_simple e))
      | Unctor (i,e) ->
        Unctor (i,(replace_simple e))
      | Match (e,branches) ->
        let branches =
          List.map
            ~f:(fun (p,e) ->
                if Lang.Pattern.contains_id i p then
                  (p,e)
                else
                  (p,replace_simple e))
            branches
        in
        Match ((replace_simple e),branches)
      | Fix (i',t,e') ->
        if Id.equal i i' then
          e
        else
          Fix (i',t,(replace_simple e'))
      | Tuple es ->
        Tuple
          (List.map ~f:replace_simple es)
      | Proj (i,e) ->
        Proj (i,(replace_simple e))
      | Abstract _ ->
        e
      | LTE (e1,e2) -> LTE (replace_simple e1,replace_simple e2)
    end

  let replace_holes
      ~(i_e:(Id.t * t) list)
      (e:t)
    : t =
    List.fold_left
      ~f:(fun acc (i,e) -> replace i e acc)
      ~init:e
      i_e

  let from_standard_exp
    : Lang.Expr.t -> t =
    Lang.Expr.fold
      ~var_f:(fun i -> Var i)
      ~eq_f:(fun b e1 e2 -> Eq (b,e1,e2))
      ~app_f:(fun e1 e2 -> App (e1,e2))
      ~func_f:(fun p e -> Func (p,e))
      ~ctor_f:(fun i e -> Ctor (i,e))
      ~unctor_f:(fun i e -> Unctor (i,e))
      ~match_f:(fun em pes -> Match (em,pes))
      ~fix_f:(fun i t e -> Fix (i,t,e))
      ~tuple_f:(fun es -> Tuple es)
      ~proj_f:(fun i e -> Proj (i,e))
      ~abstract_f:(fun id i -> Abstract (id,i))
      ~lte_f:(fun e1 e2 -> LTE (e1,e2))

  let rec to_standard_exp
      (e:t)
    : Lang.Expr.t =
    begin match e with
      | Var i -> Lang.Expr.mk_var i
      | App (e1,e2) -> Lang.Expr.mk_app (to_standard_exp e1) (to_standard_exp e2)
      | Func (p,e) -> Lang.Expr.mk_func p (to_standard_exp e)
      | Ctor (i,e) -> Lang.Expr.mk_ctor i (to_standard_exp e)
      | Unctor (i,e) -> Lang.Expr.mk_unctor i (to_standard_exp e)
      | Eq (b,e1,e2) -> Lang.Expr.mk_eq b (to_standard_exp e1) (to_standard_exp e2)
      | Match (e,pes) -> Lang.Expr.mk_match (to_standard_exp e) (List.map ~f:(fun (p,e) -> (p,to_standard_exp e)) pes)
      | Fix (i,t,e) -> Lang.Expr.mk_fix i t (to_standard_exp e)
      | Tuple es -> Lang.Expr.mk_tuple (List.map ~f:to_standard_exp es)
      | Proj (i,e) -> Lang.Expr.mk_proj i (to_standard_exp e)
      | Abstract (id,i) -> Lang.Expr.mk_abstract id i
      | LTE (e1,e2) -> Lang.Expr.mk_lte (to_standard_exp e1) (to_standard_exp e2)
    end
end

module Value = struct
  type t =
    | Func of Param.t * Expr.t
    | Ctor of Id.t * t
    | Tuple of t list
    | CallFunc of Id.t
    | Abstract of Id.t * int
  [@@deriving eq, hash, ord, show]

  let rec to_exp
      (v:t)
    : Expr.t =
    begin match v with
      | Func (p,e) -> Func (p,e)
      | Ctor (i,v) -> Ctor (i,to_exp v)
      | Tuple vs -> Tuple (List.map ~f:to_exp vs)
      | CallFunc i -> Var i
      | Abstract (id,i) -> Abstract (id,i)
    end

  let mk_true : t = Ctor ((Id.create "True"),(Tuple []))

  let mk_false : t = Ctor ((Id.create "False"),(Tuple []))

  let from_bool (b:bool) : t = if b then mk_true else mk_false

  let rec matches_pattern_and_extractions
      (p:Lang.Pattern.t)
      (v:t)
    : (Id.t * t) list option =
    begin match (p,v) with
      | (Tuple ps, Tuple vs) ->
        let merge_os =
          List.map2_exn
            ~f:matches_pattern_and_extractions
            ps
            vs
        in
        Option.map
          ~f:(fun ivs -> List.concat ivs)
          (distribute_option merge_os)
      | (Ctor (i,p),Ctor (i',v)) ->
        if Id.equal i i' then
          matches_pattern_and_extractions p v
        else
          None
      | (Var i,_) -> Some [(i,v)]
      | (Wildcard,_) -> Some []
      | _ -> failwith ("bad typechecking: pattern: " ^ Lang.Pattern.show p ^ "value: " ^ show v)
    end

  let rec size
      (v:t)
    : int =
    begin match v with
      | Func _ -> 1
      | Ctor (i,v) -> 1 + (size v)
      | Tuple vs -> IntList.sum (List.map ~f:size vs)
      | CallFunc _ -> failwith "shouldn't occur"
      | Abstract (_,i) -> i
    end
end

let rec evaluate
    (generated_context:(Id.t * Expr.t) list)
    (max_value:int)
    (e:Expr.t)
  : Value.t =
  let full_evaluate = evaluate in
  let evaluate = evaluate generated_context max_value in
  let ans =
    match e with
    | Var i -> Value.CallFunc i
    | App (e1,e2) ->
      let (v1) = evaluate e1 in
      let e1 = Value.to_exp v1 in
      begin match e1 with
        | Func ((i,_),e1) ->
          let (v2) = evaluate e2 in
          let e2 = Value.to_exp v2 in
          evaluate (Expr.replace i e2 e1)
        | Var i ->
          let v2 = evaluate e2 in
          let e = List.Assoc.find_exn ~equal:Id.equal generated_context i in
          let v2s = Value.size v2 in
          if v2s < max_value then
            full_evaluate generated_context v2s (Expr.App (e,Value.to_exp v2))
          else
            failwith "invalid rec call"
        | _ -> failwith "nonfunc applied"
      end
    | Eq (b,e1,e2) ->
      let v1 = evaluate e1 in
      let v2 = evaluate e2 in
      let eq = Value.equal v1 v2 in
      let res = if b then eq else not eq in
      Value.from_bool res
    | Func (a,e) ->
      Func (a,e)
    | Ctor (i,e) ->
      let v = evaluate e in
      Ctor (i,v)
    | Match (e,branches) as match_expr ->
      let v = evaluate e in
      let branch_o =
        List.find_map
          ~f:(fun (p,e) ->
              Option.map
                ~f:(fun ms -> (ms,e))
                (Value.matches_pattern_and_extractions p v))
          branches
      in
      let (replacements,e) =
        begin match branch_o with
          | None ->
            failwith
              ((Value.show v)
               ^ " not matched: \n "
               ^ (Expr.show match_expr))
          | Some b -> b
        end
      in
      let replacements =
        List.map ~f:(fun (i,v) -> (i,Value.to_exp v)) replacements
      in
      let v = evaluate (Expr.replace_holes ~i_e:replacements e) in
      v
    | Fix (i,_,e') ->
      evaluate (Expr.replace i e e')
    | Tuple es ->
      let vs =
        List.map ~f:evaluate es
      in
      Tuple vs
    | Proj (i,e) ->
      let v = evaluate e in
      begin match v with
        | Tuple vs -> List.nth_exn vs i
        | _ -> failwith (Expr.show e)
      end
    | Unctor (i,e) ->
      let v = evaluate e in
      begin match v with
        | Ctor (i',e) ->
          if (Id.equal i  i') then
            e
          else
            failwith ("Expected ctor " ^ Id.show i ^ " but got ctor " ^ Id.show i')
        | _ -> failwith "bad unctor"
      end
    | Abstract (id,i) ->
      Abstract (id,i)
    | LTE (e1,e2) ->
      let v1 = evaluate e1 in
      let v2 = evaluate e2 in
      begin match (v1,v2) with
        | (Abstract (id1,i1),Abstract (id2,i2)) ->
          if Id.equal id1 id2 then
            let res = i1 <= i2 in
            Value.from_bool res
          else
            failwith "bad"
        | _ -> failwith "bad"
      end
  in
  ans

let evaluate_with_holes
    ~eval_context:(i_e:(Id.t * Expr.t) list)
    (generated_context:(Id.t * Expr.t) list)
    (e:Expr.t)
  : Value.t =
  let e = Expr.replace_holes ~i_e e in
  evaluate generated_context Int.max_value e

let safe_evaluate
    (generated_context:(Id.t * Expr.t) list)
    (e:Expr.t)
  : Value.t option =
  try
    Some (evaluate generated_context Int.max_value e)
  with _ ->
    None

let safe_evaluate_with_holes
    ~(eval_context:(Id.t * Expr.t) list)
    (generated_context:(Id.t * Expr.t) list)
    (e:Expr.t)
  : Value.t option =
  try
    Some (evaluate_with_holes ~eval_context generated_context e)
  with _ ->
    None
