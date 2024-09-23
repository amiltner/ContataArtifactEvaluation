open CoreAndMore
open Lang

type t =
  {
    holes     : (Id.t * (Type.t * Type.t * Id.t list)) list ;
    predicate : Id.t -> Value.t -> Value.t -> bool          ;
    exprs     : Expr.t list                                 ;
  }
[@@deriving show]

let from_sketch
    (s:Sketch.t)
  : t =
  { holes     = s.holes ;
    predicate = s.predicate ;
    exprs     = [] ;
  }

let integrate_uf_and_inputs
    (gs:t)
    ((_,form):UniversalFormula.t)
    (assignment:(Id.t * Value.t) list)
  : t =
  let new_expr =
    Expr.replace_holes
      ~i_e:(List.map ~f:(fun (i,v) -> (i,Value.to_exp v)) assignment)
      form
  in
  { gs with exprs = new_expr::gs.exprs }

let get_hole_ids
    (gs:t)
  : Id.t list =
  List.map ~f:fst gs.holes

let get_types_exn
    (gs:t)
    (i:Id.t)
  : (Type.t * Type.t) =
  let (t1,t2,_) =
    List.Assoc.find_exn
      ~equal:Id.equal
      gs.holes
      i
  in
  (t1,t2)

let get_hole_info
    (gs:t)
    (i:Id.t)
  : (Type.t * Type.t * (Id.t list)) =
  List.Assoc.find_exn
    ~equal:Id.equal
    gs.holes
    i
