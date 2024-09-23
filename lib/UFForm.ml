open CoreAndMore
open Lang
module MyLog = Log
open Z3
module Log = MyLog

(* DO NOT USE THIS MODULE IN A CONCURRENT SETTING *)

type 'a memoizer =
  {
    mutable as_z3 : Z3.Expr.expr option ;
    mutable decl  : FuncDecl.func_decl option ;
    node : 'a ;
  }

let equal_memoizer node_equal x y = node_equal x.node y.node
let compare_memoizer node_compare x y = node_compare x.node y.node
let pp_memoizer node_pp formatter x = node_pp formatter x.node
let hash_fold_memoizer node_hash_fold state x = node_hash_fold state x.node

type t = l hash_consed
and l = t_node memoizer
and t_node =
  | FC of Id.t * Value.t * Value.t
  | And of t list
  | Or of t list
  | Not of t
[@@deriving eq, hash, ord, show]

let table = HashConsTable.create 100000
let hashcons = HashConsTable.hashcons hash_l compare_l table

module IdMap = HashTable.Make(Id)
module IntMap = HashTable.Make(IntModule)
let func_decls : FuncDecl.func_decl IdMap.t = IdMap.empty ()
let uid_to_value : Value.t IntMap.t = IntMap.empty ()

let create (node:t_node) =
  hashcons { node; as_z3 = None; decl = None; }
let node (t:t) = t.node.node
let uid (f:t) = f.tag

let ctx = Z3.mk_context [("unsat_core","true");("proof","false")]
let int_sort = Z3.Arithmetic.Integer.mk_sort ctx
let solver = Solver.mk_simple_solver ctx

let not_ v = create (Not v)
let true_ = create (And [])
let false_ = create (Or [])

let destruct_or
    (r:t)
  : t list option =
  begin match node r with
    | Or rs -> Some rs
    | _ -> None
  end

let destruct_and
    (r:t)
  : t list option =
  begin match node r with
    | And rs -> Some rs
    | _ -> None
  end

let destruct_fc
    (r:t)
  : (Id.t * Value.t * Value.t) option =
  begin match node r with
    | FC (i,vin,vout) -> Some (i,vin,vout)
    | _ -> None
  end

let destruct_fc_exn
    (r:t)
  : Id.t * Value.t * Value.t =
  Option.value_exn (destruct_fc r)

let fc i v1 v2 =
  let res = create (FC (i,v1,v2)) in
  begin match res.node.decl with
    | None ->
      let decl =
        IdMap.find_or_add
          i
          (fun () ->
             FuncDecl.mk_func_decl
               ctx
               (Z3.Symbol.mk_string ctx (Id.to_string i))
               [int_sort]
               int_sort)
          func_decls
      in
      IntMap.add v1.tag v1 uid_to_value;
      IntMap.add v2.tag v2 uid_to_value;
      res.node.decl <- Some decl;
    | Some _ -> ()
  end;
  res
let rec explode_ands vs =
  List.concat_map
    ~f:(fun v ->
        begin match destruct_and v with
          | Some vs -> explode_ands vs
          | _ -> [v]
        end)
    vs
let and_ vs =
  begin match explode_ands vs with
    | [x] -> x
    | exploded ->
      if List.exists ~f:(equal false_) exploded then
        false_
      else
        create (And exploded)
    end
let rec explode_ors vs =
  List.concat_map
    ~f:(fun v ->
        begin match destruct_or v with
          | Some vs -> explode_ors vs
          | _ -> [v]
        end)
    vs
let or_ vs =
  begin match explode_ors vs with
    | [x] -> x
    | exploded ->
      if List.exists ~f:(equal true_) exploded then
        true_
      else
        create (Or exploded)
    end
let band v1 v2 = and_ [v1;v2]
let bor v1 v2 = or_ [v1;v2]
let implies v1 v2 = bor (not_ v1) v2

let rec fold
    ~(fc:Id.t -> Value.t -> Value.t -> 'a)
    ~(and_:'a list -> 'a)
    ~(or_:'a list -> 'a)
    ~(not_:'a -> 'a)
    (f:t)
  : 'a =
  let fold_recurse = fold ~fc ~and_ ~or_ ~not_ in
  begin match node f with
    | FC (i,v1,v2) -> fc i v1 v2
    | And vs -> and_ (List.map ~f:fold_recurse vs)
    | Or vs -> or_ (List.map ~f:fold_recurse vs)
    | Not v -> not_ (fold_recurse v)
  end

let extract_all_fns
    (f:t)
  : Id.t list =
  let rec extract_all_fns f =
    begin match node f with
      | FC (i,_,_) -> [i]
      | And fs -> List.concat_map ~f:extract_all_fns fs
      | Or fs -> List.concat_map ~f:extract_all_fns fs
      | Not f -> extract_all_fns f
    end
  in
  List.dedup_and_sort ~compare:Id.compare (extract_all_fns f)

let rec to_z3
    (f:t)
  : Z3.Expr.expr =
  begin match f.node.as_z3 with
    | Some z3 -> z3
    | None ->
      let result =
        begin match node f with
          | FC (i,v1,v2) ->
            Boolean.mk_eq
              ctx
              (Expr.mk_app
                 ctx
                 (Option.value_exn f.node.decl)
                 [Arithmetic.Integer.mk_numeral_i ctx v1.tag])
              (Arithmetic.Integer.mk_numeral_i ctx v2.tag)
          | And fs ->
            Boolean.mk_and
              ctx
              (List.map ~f:to_z3 fs)
          | Or fs ->
            Boolean.mk_or
              ctx
              (List.map ~f:to_z3 fs)
          | Not f ->
            Boolean.mk_not
              ctx
              (to_z3 f)
        end
      in
      f.node.as_z3 <- Some result;
      result
  end

let satisfiable
    (f:t)
  : bool =
  Log.z3 (fun () -> "Checking " ^ show f);
  Consts.time
    Consts.z3_times
    (fun () ->
       Z3.Solver.push solver;
       Solver.add solver [to_z3 f];
       let result =
         begin match Solver.check solver [] with
           | SATISFIABLE ->
             Log.z3 (fun () -> "Determined Satisfiable");
             true
           | UNSATISFIABLE ->
             Log.z3 (fun () -> "Determined Unsatisfiable");
             false
           | UNKNOWN ->
             failwith "unknown satisfiability result"
         end
       in
       Z3.Solver.pop solver 1;
       result)

let valid
    (f:t)
  : bool =
  not (satisfiable (not_ f))

let implication_comparison x y =
  let x_implies_y = valid (implies x y) in
  let y_implies_x = valid (implies y x) in
  begin match (x_implies_y,y_implies_x) with
    | (true,true) -> CoreAndMore.PO_EQ
    | (true,false) -> CoreAndMore.PO_GT
    | (false,true) -> CoreAndMore.PO_LT
    | (false,false) -> CoreAndMore.PO_INCOMPARABLE
  end

let all_calls : t -> (Id.t * Value.t) list =
  fold
    ~fc:(fun i v1 _ -> [(i,v1)])
    ~and_:List.concat
    ~or_:List.concat
    ~not_:Fn.id

let extract_fn_call_equality_exn
    (e:Z3.Expr.expr)
  : (Id.t * Value.t * Value.t) =
  let eqargs = Expr.get_args e in
  begin match eqargs with
    | [fcall;expresult] ->
      let res = Z.to_int (Z3.Arithmetic.Integer.get_big_int expresult) in
      let vout = Option.value_exn (IntMap.find_opt res uid_to_value) in
      let fd = Z3.Expr.get_func_decl fcall in
      let fid = Id.create (Z3.Symbol.get_string (Z3.FuncDecl.get_name fd)) in
      let farg = Expr.get_args fcall in
      begin match farg with
        | [x] ->
          let arg = Z.to_int (Z3.Arithmetic.Integer.get_big_int x) in
          let vin = Option.value_exn (IntMap.find_opt arg uid_to_value) in
          (fid,vin,vout)
        | _ -> failwith "invalid fn call"
      end
    | _ -> failwith "invalid fn call"
  end


let check_and_get_model
    (basis:t)
    (fs:t list)
  : t list option =
  Log.z3
    (fun () ->
       "Checking " ^
       (string_of_list show fs) ^
       " Implies " ^
       (show basis));
  Consts.time
    Consts.z3_times
    (fun () ->
       Z3.Solver.push solver;
       Solver.add solver [to_z3 basis];
       let id_to_form = IntMap.empty () in
       let counter = ref 0 in
       List.iter
         ~f:(fun f ->
             IntMap.add !counter f id_to_form;
             Solver.assert_and_track
               solver
               (to_z3 f)
               (Z3.Boolean.mk_const ctx (Symbol.mk_int ctx !counter));
             counter := !counter+1;
             ())
         fs;
       let result =
         begin match Solver.check solver [] with
           | SATISFIABLE ->
             Log.z3 (fun () -> "Determined Satisfiable");
             None
           | UNSATISFIABLE ->
             Log.z3 (fun () -> "Determined Unsatisfiable");
             let core = Solver.get_unsat_core solver in
             Some
               (List.map
                  ~f:(fun c ->
                      let cd = Z3.Expr.get_func_decl c in
                      let i = Z3.Symbol.get_int (Z3.FuncDecl.get_name cd) in
                      Option.value_exn (IntMap.find_opt i id_to_form))
                  core)
           | UNKNOWN ->
             failwith "unknown satisfiability result"
         end
       in
       Z3.Solver.pop solver 1;
       result)

type iterative_checker_argument =
  | NextElement of t
  | Terminate

type iterative_checker_result =
  | UserTerminated
  | Unsat of t list
  | Continue of (iterative_checker_argument -> iterative_checker_result)

(*Be careful using this. Make sure you terminate it's usage*)
let iteratively_check
    (basis:t)
  : iterative_checker_argument -> iterative_checker_result =
  Log.z3
    (fun () ->
       "Begun iterative checker with basis " ^ (show basis));
  Z3.Solver.push solver;
  Solver.add solver [to_z3 basis];
  let cleanup () = Z3.Solver.pop solver 1 in
  let counter = ref 1 in
  let id_to_form = IntMap.empty () in
  let rec check_next arg =
    begin match arg with
      | Terminate -> cleanup (); UserTerminated
      | NextElement f ->
        Consts.time
          Consts.z3_times
          (fun () ->
             IntMap.add !counter f id_to_form;
             Solver.assert_and_track
               solver
               (to_z3 f)
               (Z3.Boolean.mk_const ctx (Symbol.mk_int ctx !counter));
             counter := !counter+1;
             begin match Solver.check solver [] with
               | SATISFIABLE ->
                 Log.z3 (fun () -> "Thus far determined satisfiable");
                 Continue check_next
               | UNSATISFIABLE ->
                 Log.z3 (fun () -> "Determined Unsatisfiable");
                 let core = Solver.get_unsat_core solver in
                 cleanup ();
                 Unsat
                   (List.map
                      ~f:(fun c ->
                          let cd = Z3.Expr.get_func_decl c in
                          let i = Z3.Symbol.get_int (Z3.FuncDecl.get_name cd) in
                          Option.value_exn (IntMap.find_opt i id_to_form))
                      core)
               | UNKNOWN ->
                 failwith "unknown satisfiability result"
             end)
    end
  in
  check_next
