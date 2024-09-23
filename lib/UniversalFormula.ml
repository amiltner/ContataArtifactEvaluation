open CoreAndMore
open Lang

module Make(L:Language.S) = struct
  module L = L
  type t = (Id.t * L.Type.t) list * L.Expr.t
  [@@deriving eq, hash, ord, show]

  (*let to_expr_and_type
      ((ps,e):t)
    : Expr.t * Type.t =
    let e =
      List.fold_right
        ~f:(Expr.mk_func)
        ~init:e
        ps
    in
    let t =
      List.fold_right
        ~f:(fun (_,t1) t2 -> Type.mk_arrow t1 t2)
        ~init:Type._bool
        ps
    in
    (e,t)

  let to_param_types
      ((ps,e):t)
    : Type.t list =
    List.map ~f:snd ps

  let to_param_ids
      ((ps,e):t)
    : Id.t list =
    List.map ~f:fst ps

  let to_exp
      ((ps,e):t)
    : Expr.t =
    e*)
end

type t =
  Param.t list * Expr.t
[@@deriving eq, hash, ord, show]

let to_expr_and_type
    ((ps,e):t)
  : Expr.t * Type.t =
  let e =
    List.fold_right
      ~f:(Expr.mk_func)
      ~init:e
      ps
  in
  let t =
    List.fold_right
      ~f:(fun (_,t1) t2 -> Type.mk_arrow t1 t2)
      ~init:Type._bool
      ps
  in
  (e,t)

let to_param_types
    ((ps,e):t)
  : Type.t list =
  List.map ~f:snd ps

let to_param_ids
    ((ps,e):t)
  : Id.t list =
  List.map ~f:fst ps

let to_exp
    ((ps,e):t)
  : Expr.t =
  e
