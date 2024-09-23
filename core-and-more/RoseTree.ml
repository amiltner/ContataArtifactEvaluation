open Core
open Util

(* This is to open core for deriving, but keep closed eleswhere*)
module RoseTreeContainer = struct
  type 'a rose_tree = RoseTreeNode of ('a * ('a rose_tree) list)
  [@@deriving show, hash, eq, ord]

  let rec fold_over_rose_tree_elements
      ~(init:'b)
      ~(f:'b -> 'a -> 'b)
      (RoseTreeNode (x,ts):'a rose_tree)
    : 'b =
    let init = f init x in
    List.fold
      ~f:(fun init t ->
          fold_over_rose_tree_elements
            ~init
            ~f
            t)
      ~init
      ts

  let rec fold_rose_tree
      ~(f:'b list -> 'a -> 'b)
      (RoseTreeNode (x,ts):'a rose_tree)
    : 'b =
    let bs = List.map ~f:(fold_rose_tree ~f) ts in
    f bs x

  let flatten_rose_tree
      (x:'a rose_tree)
    : 'a list =
    fold_over_rose_tree_elements
      ~f:(fun acc x -> x::acc)
      ~init:[]
      x
end
include RoseTreeContainer

(* Functorial interface *)
module RoseTreeOf(D:Data) = struct
  type t = D.t rose_tree
  [@@deriving show, hash, eq, ord]

  let rec fold_over_elements
      ~(init:'b)
      ~(f:'b -> D.t -> 'b)
      (RoseTreeNode (x,ts):t)
    : 'b =
    let init = f init x in
    List.fold
      ~f:(fun init t ->
          fold_over_elements
            ~init
            ~f
            t)
      ~init
      ts

  let rec fold
      ~(f:'b list -> D.t -> 'b)
      (RoseTreeNode (x,ts):t)
    : 'b =
    let bs = List.map ~f:(fold ~f) ts in
    f bs x
end
