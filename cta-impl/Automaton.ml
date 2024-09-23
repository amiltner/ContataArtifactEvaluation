module type Config = sig
  include CoreAndMore.Data

  val product : t -> t -> t option
end

(** Find or creates an element in a Hastbl.
    e is the key. If no element is mapped to e,
    (f e) is mapped to it and retuned. *)
let find_or_create f map e =
  match Hashtbl.find_opt map e with
  | Some x -> x
  | None ->
    let x = f e in
    Hashtbl.add map e x;
    x

module Make
    (F : Symbol.S)
    (L : Logic.S)
    (Q : State.S with type logic = L.t) = struct
  module Symbol = F
  module State = Q
  module Logic = L

  module Configuration = Configuration.Make(State)(Symbol)(Logic)

  module StateP = struct
    include State
  end

  module StateSet = CoreAndMore.HashSet.HSWrapper (StateP)
  module StateMap = CoreAndMore.HashTable.Make(StateP)

  module ConfigurationSet = CoreAndMore.HashSet.HSWrapper (Configuration)
  module ConfigurationMap = CoreAndMore.HashTable.Make (Configuration)

  type t = {
    mutable roots : StateSet.t; (* Final states. *)
    state_confs : ConfigurationSet.t StateMap.t; (* Associates to each state the set of configurations leading to it. *)
    conf_states : StateSet.t ConfigurationMap.t; (* Associates to each configuration the set of states to go to. *)
    state_parents : ConfigurationSet.t StateMap.t (* Associates to each state the set of configurations it appears in. *)
  }

  type data = unit

  let empty () = {
    roots = (StateSet.empty ());
    state_confs = StateMap.empty ();
    conf_states = ConfigurationMap.create 50;
    state_parents = StateMap.empty () ;
  }

  let create _ = empty ()

  let data _ = ()

  let clear _ = empty ()

  let copy x =
    let state_confs = StateMap.empty () in
    StateMap.iter
      (fun k cs ->
         if not (ConfigurationSet.is_empty cs) then
           StateMap.add k (ConfigurationSet.copy cs) state_confs)
      x.state_confs;
    let conf_states = ConfigurationMap.empty () in
    ConfigurationMap.iter
      (fun k ss ->
         if not (StateSet.is_empty ss) then
           ConfigurationMap.add k (StateSet.copy ss) conf_states)
      x.conf_states;
    let state_parents = StateMap.empty () in
    StateMap.iter
      (fun k cs ->
         if not (ConfigurationSet.is_empty cs) then
           StateMap.add k (ConfigurationSet.copy cs) state_parents)
      x.state_parents;
    {
      roots = StateSet.copy x.roots ;
      state_confs = state_confs ;
      conf_states = conf_states ;
      state_parents = state_parents ;
    }

  let final_state_set a = a.roots

  let final_states a =
    StateSet.as_list
      (final_state_set a)

  let configurations_for_states a =
    a.state_confs

  let states_for_configurations a =
    a.conf_states

  let state_parents q a =
    StateMap.find_or_add
      q
      (fun () -> (ConfigurationSet.empty ()))
      a.state_parents

  let add_final_state a q =
    StateSet.add q a.roots

  let remove_final_state a q =
    StateSet.remove q a.roots

  let add_final_states a set =
    StateSet.iter
      (fun e -> StateSet.add e a.roots)
      set

  let set_final_states a set =
    a.roots <- set

  type hook = Configuration.t -> State.t -> unit

  let configurations_for_state q a =
    StateMap.find_or_add
      q
      (fun _ -> ConfigurationSet.empty ())
      a.state_confs

  let configurations_for_state_nonmutate q a =
    begin match StateMap.find_opt q a.state_confs with
      | None -> ConfigurationSet.create 0
      | Some cs -> cs
    end

  let states_for_configuration conf a =
    ConfigurationMap.find_or_add
      conf
      (fun _ -> StateSet.empty ())
      a.conf_states

  let add_transition (conf) q (a:t) =
    let add_parent_to q =
      let cs = state_parents q a in
      ConfigurationSet.add
        conf
        cs;
    in
    ConfigurationSet.add (conf) (configurations_for_state q a);
    StateSet.add q (states_for_configuration conf a);
    List.iter add_parent_to (conf.sources)

  let remove_transition (conf) q (a:t) =
    let remove_parent_from q =
      let cs = (state_parents q a) in
      (ConfigurationSet.remove conf cs);
    in
    ConfigurationSet.remove conf (configurations_for_state q a);
    let sc = states_for_configuration conf a in
    StateSet.remove q sc;
    if StateSet.is_empty sc then
      List.iter remove_parent_from conf.sources
    else
      ()

  type transition = Configuration.t * State.t

  module Option = struct
    let product f a b =
      match a, b with
      | Some a, Some b ->
        begin match f a b with
          | Some p -> Some (Some p)
          | None -> None
        end
      | None, None -> Some None
      | Some a, _ -> Some (Some a)
      | _, Some b -> Some (Some b)

    let compare f a b =
      match a, b with
      | Some a, Some b -> f a b
      | Some _, None -> 1
      | None, Some _ -> -1
      | None, None -> 0

    let equal f a b =
      match a, b with
      | Some a, Some b -> f a b
      | None, None -> true
      | _, _ -> false

    let hash f = function
      | Some lq -> f lq
      | None -> 0

    let print f t out =
      match t with
      | Some lq -> f lq out
      | None -> Format.fprintf out "~"
  end

  module Binding = struct
    let hash_fold_option = CoreAndMore.hash_fold_option
    type t = State.t option
    [@@deriving hash]

    let product qa qb =
      match Option.product State.product qa qb with
      | Some q -> Some (q)
      | _ -> None

    let compare qa qb =
      Option.compare State.compare qa qb

    let equal qa qb =
      Option.equal State.equal qa qb

    let hash (q : t) = Option.hash State.hash q

    let pp out q =
      Format.fprintf out ":%t" (Option.print (fun x y -> State.pp y x) q)

    let show = CoreAndMore.show_of_pp pp
  end

  module SymSet = Set.Make (Symbol)

  let is_state_empty q a =
    let confs = configurations_for_state q a in
    ConfigurationSet.is_empty confs

  let fold_transitions f a x =
    let fold_state_confs q confs x =
      let fold_labeled_confs conf = f conf q in
      ConfigurationSet.fold (fold_labeled_confs) confs x
    in
    StateMap.fold (fold_state_confs) (configurations_for_states a) x

  let fold_states f a x =
    let table = Hashtbl.create 8 in
    let uniq_f q x =
      match Hashtbl.find_opt table q with
      | Some () -> x
      | None ->
        Hashtbl.add table q ();
        f q x
    in
    let rec fold_state q x =
      match Hashtbl.find_opt table q with
      | Some () -> x
      | None ->
        Hashtbl.add table q ();
        ConfigurationSet.fold (fold_configuration) (configurations_for_state_nonmutate q a) (f q x)
    and fold_configuration conf x =
      let ss = conf.sources in
      List.fold_right fold_state ss x
    and fold_transition conf q x =
      fold_configuration conf (uniq_f q x)
    in
    let x = StateSet.fold (uniq_f) (final_state_set a) x in
    fold_transitions (fold_transition) a x

  let state_set a =
    let ss = StateSet.empty () in
    fold_states (fun x () -> StateSet.add x ss) a ();
    ss

  let states a = fold_states List.cons a []

  let is_final_state a q =
    StateSet.contains q (final_state_set a)

  let state_count a =
    fold_states (fun _ k -> k + 1) a 0

  let mem conf _ state a =
    let states = states_for_configuration conf a in
    StateSet.contains state states

  let mem_configuration conf a =
    begin match ConfigurationMap.find_opt conf (states_for_configurations a) with
      | Some _ -> true
      | None -> false
    end

  let mem_state q a =
    begin match StateMap.find_opt q (configurations_for_states a) with
      | None -> false
      | Some _ -> true
    end || StateSet.contains q (final_state_set a)

  let rec fold_configurations_for_binding func ty t x =
    match ty with
    | (Some q, _) ->
      let confs = configurations_for_state q t in
      let foreach_conf conf x =
        func conf q x
      in
      ConfigurationSet.fold foreach_conf confs x
    | (None, label) ->
      let foreach_state q x =
        fold_configurations_for_binding func (Some q, label) t x
      in
      fold_states foreach_state t x

  let iter_configurations_for_binding f ty t =
    fold_configurations_for_binding (fun c q () -> f c q) ty t ()

  let list_map_opt f l =
    let for_each_element e = function
      | Some acc ->
        begin
          match f e with
          | Some e -> Some (e::acc)
          | None -> None
        end
      | None -> None
    in
    List.fold_right for_each_element l (Some [])

  let rec list_map2_opt f l1 l2 =
    match l1, l2 with
    | [], [] -> Some []
    | e1::l1, e2::l2 ->
      begin
        match list_map2_opt f l1 l2 with
        | Some l ->
          begin
            match f e1 e2 with
            | Some e -> Some (e::l)
            | None -> None
          end
        | None -> None
      end
    | _, _ -> None

  let label f default _ = (* FIXME why is the automaton not used? *)
    let table = Hashtbl.create 8 in
    let rec label q : 'a =
      match Hashtbl.find_opt table q with
      | Some (Some v) -> v (* label is already computed *)
      | Some (None) -> default q (* label is being computed (cycle) *)
      | None -> (* label is not computed *)
        Hashtbl.add table q None;
        let v = f label q in
        Hashtbl.add table q (Some v);
        v
    in label

  type normalizer = Symbol.t -> State.t list -> State.t

  let filter p t =
    let aut = empty () in
    let add conf q () =
      if p conf label q then
        add_transition conf q aut
      else
        ()
    in
    fold_transitions add t ();
    let add_final q =
      add_final_state aut q
    in
    StateSet.iter add_final (final_state_set t);
    aut


  let sub_automaton states t =
    let u = empty () in
    let visited = Hashtbl.create 8 in
    let rec visit_state q () =
      match Hashtbl.find_opt visited q with
      | Some () -> ()
      | None ->
        Hashtbl.add visited q ();
        let confs = configurations_for_state q t in
        let add_conf conf () =
          let u = add_transition conf q u in
          visit_conf conf u
        in
        ConfigurationSet.fold add_conf confs ()
    and visit_conf_internal (conf:Configuration.t) () =
      List.fold_right visit_state (conf.sources) ()
    and visit_conf x _ = visit_conf_internal x ()
    in
    (set_final_states u states);
    StateSet.fold visit_state states ();
    u

  let intersect initials a b =
    let aut = empty () in
    let added_states = StateSet.empty () in
    (*let processed_configs = ConfigurationSet.empty () in*)
    let initial_configs =
      List.concat_map
        (fun (label,constrt) ->
           let config = Configuration.make ~sources:[] ~label ~constrt in
           let full_ss =
             StateSet.fold2
               (fun a_state b_state ss -> (a_state,b_state)::ss)
               (states_for_configuration config a)
               (states_for_configuration config b)
               []
           in
           List.map
             (fun (a,b) -> (config,a,b))
             full_ss)
        initials
    in
    let add_configs
        (configs)
      : unit =
      let continuing = ref true in
      let configs_ref = ref configs in
      while !continuing do
        begin match !configs_ref with
          | [] -> continuing := false
          | (config,s1,s2)::t ->
            begin match State.product s1 s2 with
              | None ->
                configs_ref := t
              | Some s ->
                add_transition config s aut;
                if StateSet.contains s added_states then
                  configs_ref := t
                else
                  begin
                    StateSet.add s added_states;
                    let configs =
                      ConfigurationSet.fold2
                        (fun c1 c2 cs ->
                           begin match Configuration.product c1 c2 with
                             | None -> cs
                             | Some p -> (c1,c2,p)::cs
                           end)
                        (state_parents s1 a)
                        (state_parents s2 b)
                        []
                    in
                    let configs_output =
                      List.concat_map
                        (fun ((c1,c2,c):(Configuration.t*Configuration.t*Configuration.t)) ->
                           (*if ConfigurationSet.contains c processed_configs then
                             []
                             else*)
                           let ss = c.sources in
                           if List.for_all
                               (fun s -> StateSet.contains s added_states)
                               ss
                           then
                             begin
                               (*ConfigurationSet.add c processed_configs;*)
                               StateSet.fold2
                                 (fun s1 s2 sps ->
                                    (c,s1,s2)::sps
                                 )
                                 (states_for_configuration c1 a)
                                 (states_for_configuration c2 b)
                                 []
                             end
                           else
                             [])
                        configs
                    in
                    configs_ref := configs_output@t;
                  end
            end
        end
      done;
    in
    let _ = add_configs initial_configs in
    StateSet.fold2
      (fun s1 s2 () ->
         begin match State.product s1 s2 with
           | None -> ()
           | Some s ->
             if StateSet.contains s added_states then
               add_final_state aut s
             else
               ()
         end)
      (final_state_set a)
      (final_state_set b)
      ();
    aut

  let reachable_states a =
    let visited = Hashtbl.create 8 in
    let reachable set c = StateSet.contains c set in
    let set = StateSet.empty () in
    let rec reach_conf conf set =
      reach_conf_states conf (states_for_configuration conf a) set
    and reach_conf_states conf lbl_states () =
      let ss = conf.sources in
      let fold q () =
        match Hashtbl.find_opt visited q with
        | Some () -> ()
        | None ->
          Hashtbl.add visited q ();
          ConfigurationSet.fold (reach_conf) (state_parents q a) (StateSet.add q set)
      in
      if (List.for_all (reachable set) ss) then
        StateSet.fold (fold) lbl_states ()
      else ()
    in
    ConfigurationMap.fold (reach_conf_states) ((states_for_configurations a)) ();
    set

  let reduce ?(from_finals=true) t =
    let rt = empty () in
    let reachable_states = reachable_states t in
    let is_reachable_state q = StateSet.contains q reachable_states in
    let is_reachable_conf (c:Configuration.t) =
      let ss = c.sources in
      List.for_all is_reachable_state ss in
    let for_each_transition conf q () =
      if is_reachable_state q && is_reachable_conf conf then
        add_transition conf q rt
      else
        ()
    in
    fold_transitions for_each_transition t ();
    let for_each_final_state q () =
      if is_reachable_state q then
        add_final_state rt q
      else ()
    in
    (if from_finals then
       StateSet.fold for_each_final_state (final_state_set t) ()
     else
       fold_states for_each_final_state t ());
    rt

  let add_transition a label constrt sources st =
    add_transition
      (Configuration.make
         ~sources
         ~label
         ~constrt)
      st
      a

  let prune_useless_full (x:t)
    : t =
    let x = reduce x in
    let fs = final_state_set x in
    let x = sub_automaton fs x in
    x

  let prune_useless (x:t)
    : t =
    (*let x = reduce x in*)
    let fs = final_state_set x in
    let x = sub_automaton fs x in
    x

  type renaming = State.t StateMap.t

  exception Found of renaming

  let print t out =
    let print_state_confs q confs =
      let print_conf conf =
        Format.fprintf out "%t -> %t\n" (fun f -> Configuration.pp f conf) ((fun x y -> State.pp y x) q)
      in
      ConfigurationSet.iter (print_conf) confs
    and print_state q =
      Format.fprintf out "%t " ((fun x y -> State.pp y x) q)
    in
    Format.fprintf out "States ";
    StateSet.iter print_state (state_set t);
    Format.fprintf out "\n\nFinal States ";
    StateSet.iter print_state (final_state_set t);
    Format.fprintf out "\n\nTransitions\n";
    StateMap.iter print_state_confs (configurations_for_states t)

  let pp f a = print a f

  open CoreAndMore

  let has_state
      a
      s
    =
    StateSet.contains s (state_set a)

  let size = state_count

  let minimize = prune_useless

  let transitions
      (c:t)
    : (Symbol.t * (State.t list) * Logic.t * State.t) list =
    fold_transitions
      (fun config s acc -> (config.label,config.sources,config.constrt,s)::acc)
      c
      []

  let transitions_from a s =
    let ps = state_parents s a in
    let cs = ConfigurationSet.as_list ps in
    List.concat_map
      ~f:(fun c ->
          let ss =
            StateSet.as_list
              (states_for_configuration c a)
          in
          List.map ~f:(fun s -> (c.label,c.sources,c.constrt,s)) ss)
      cs

  let transitions_to
      a
      s
    : Configuration.t list =
    let configs =
      configurations_for_state
        s
        a
    in
    (ConfigurationSet.as_list configs)

  module OldTerm = Term
  module Term = Term.Make(Symbol)


  module OldTermState = TermState
  module TermState = TermState.Make(Symbol)(State)

  module OldTermStateSemiring = TermStateSemiring
  module TermStateSemiring = TermStateSemiring.Make(Symbol)(State)(Logic)

  let compare_terms
      ((c1,r1s,_):Float.t * Logic.t * TermState.t)
      ((c2,r2s,_):Float.t * Logic.t * TermState.t)
    : partial_order_comparison =
    let cc =
      Float.(
        if c1 <. c2 then
          PO_LT
        else if c1 >. c2 then
          PO_GT
        else
          PO_EQ)
    in
    let rc = Logic.implication_comparison r1s r2s in
    begin match (cc,rc) with
      | (PO_INCOMPARABLE, _) -> PO_INCOMPARABLE
      | (_, PO_INCOMPARABLE) -> PO_INCOMPARABLE
      | (PO_EQ, _) -> rc
      | (_, PO_EQ) -> cc
      | (PO_LT, PO_LT) -> PO_LT
      | (PO_GT, PO_GT) -> PO_GT
      | _ -> PO_INCOMPARABLE
    end

  let extract_minimal_list
      (ls:(Float.t * Logic.t * TermState.t) list)
      (input:(Float.t * Logic.t * TermState.t))
    : (Float.t * Logic.t * TermState.t) list option =
    let rec extract_minimal_list_internal
        (acc:(Float.t * Logic.t * TermState.t) list)
        (ls:(Float.t * Logic.t * TermState.t) list)
      : (Float.t * Logic.t * TermState.t) list option =
      begin match ls with
        | [] ->
          Some (input::acc)
        | h::t ->
          begin match compare_terms input h with
            | PO_INCOMPARABLE ->
              extract_minimal_list_internal
                (h::acc)
                t
            | PO_EQ | PO_GT ->
              None
            | PO_LT ->
              extract_minimal_list_internal
                acc
                t
          end

      end
    in
    let mlo = extract_minimal_list_internal [] ls in
    Option.map ~f:(List.sort ~compare:(triple_compare Float.compare Logic.compare TermState.compare)) mlo

  module TSData = ListOf(TripleOf(FloatModule)(Logic)(TermState))
  module StateToTS = DictOf(State)(TSData)
  module TSPQ = PriorityQueueOf(struct
      module Priority = FloatModule
      type t = Float.t * Logic.t * TermState.t * State.t
      [@@deriving eq, hash, ord, show]
      let priority = fun (x,_,_,_) -> x
    end)
  let min_term_state
      ~(f:TermState.t -> bool)
      ~(cost:TermState.t -> Float.t)
      ~(base_formula:Logic.t)
      (a:t)
    : TermState.t option =
    let pops = ref 0 in
    let get_produced_from
        (st:StateToTS.t)
        (t:Symbol.t)
        (s:State.t)
        (constrt:Logic.t)
        (ss:State.t list)
      : (Float.t * Logic.t * TermState.t) list =
      let subs =
        List.map
          ~f:(fun s -> StateToTS.lookup_default ~default:[] st s)
          ss
      in
      List.filter_map
        ~f:(fun iss ->
            let (_,cs,ss) = List.unzip3 iss in
            let ts = OldTermState.TermState (t,s,ss) in
            let reqs = Logic.and_ (constrt::cs) in
            if Logic.satisfiable reqs then
              let size = cost ts in
              Some (size,reqs,OldTermState.TermState (t,s,ss))
            else
              None)
        (combinations subs)
    in
    let rec min_tree_internal
        (st:StateToTS.t)
        (pq:TSPQ.t)
      : TermState.t option =
      pops := !pops+1;
      begin match TSPQ.pop pq with
        | Some ((c,rs,t,s),_,pq) ->
          if f t then
            if is_final_state a s &&
               Logic.satisfiable (Logic.band rs (State.logic_rep s)) then
              begin
                Some t
              end
            else
              begin match StateToTS.lookup st s with
                | None ->
                  let st = StateToTS.insert st s [(c,rs,t)] in
                  let triggered_transitions = transitions_from a s in
                  let produced =
                    List.concat_map
                      ~f:(fun (t,ss,constrt,s) ->
                          List.map
                            ~f:(fun (i,ss,t) -> (i,ss,t,s))
                            (get_produced_from st t s constrt ss))
                      triggered_transitions
                  in
                  let pq = TSPQ.push_all pq produced in
                  min_tree_internal st pq
                | Some ts ->
                  begin match extract_minimal_list ts (c,rs,t) with
                    | None ->
                      min_tree_internal st pq
                    | Some ml ->
                      let st = StateToTS.insert st s ml in
                      let st_for_produced = StateToTS.insert st s [(c,rs,t)] in
                      let triggered_transitions = transitions_from a s in
                      let produced =
                        List.concat_map
                          ~f:(fun (t,ss,constrt,s) ->
                              List.map
                                ~f:(fun (i,ss,t) -> (i,ss,t,s))
                                (get_produced_from st_for_produced t s constrt ss))
                          triggered_transitions
                      in
                      let pq = TSPQ.push_all pq produced in
                      min_tree_internal st pq
                  end
              end
          else
            min_tree_internal st pq
        | None ->
          None
      end
    in
    let initial_terms =
      List.concat_map
        ~f:(fun (t,ss,c,s) ->
            List.map
              ~f:(fun (i,logic,t) -> (i,Logic.band logic base_formula,t,s))
              (get_produced_from StateToTS.empty t s c ss))
        (transitions a)
    in
    min_tree_internal
      StateToTS.empty
      (TSPQ.from_list initial_terms)

  let accepting_term_state (a:t) (t:Term.t) : TermState.t option =
    let rec accepting_term_state_state t q =
      begin match t with
        | OldTerm.Term (i,ts) ->
          List.find_map
            ~f:(fun c ->
                if Symbol.equal i c.label then
                  let ts_ss = List.zip_exn ts c.sources in
                  Option.map
                    ~f:(fun ts -> OldTermState.TermState (i,q,ts))
                    (distribute_option
                       (List.map
                          ~f:(uncurry accepting_term_state_state)
                          ts_ss))
                else
                  None)
            (transitions_to a q)
      end
    in
    List.find_map ~f:(accepting_term_state_state t) (final_states a)

  let all_accepting_term_states
      (a:t)
      (t:Term.t)
    : TermStateSemiring.t =
    let rec accepting_term_state_semiring_state req t q =
      let OldTerm.Term (outer_symbol,sub_symbols) = t in
      TermStateSemiring.one_of
        (List.map
           ~f:(fun c ->
               if Symbol.equal outer_symbol c.label then
                 let req =
                   Logic.band
                     req
                     c.constrt
                 in
                 if not (Logic.satisfiable req) then
                   TermStateSemiring.false_
                 else
                   TermStateSemiring.transition
                     outer_symbol
                     q
                     c.constrt
                     (List.map2_exn
                        ~f:(accepting_term_state_semiring_state req)
                        sub_symbols
                        c.sources)
               else
                 TermStateSemiring.false_)
           (transitions_to a q))
    in
    let anses =
      List.map
        ~f:(fun s ->
            let f = State.logic_rep s in
            TermStateSemiring.final_logic
              f
              (accepting_term_state_semiring_state f t s))
        (final_states a)
    in
    TermStateSemiring.one_of anses

  let all_accepting_logic
      (a:t)
      (t:Term.t)
    : Logic.t =
    let tss = all_accepting_term_states a t in
    let rec tss_to_logic tss =
      begin match tss with
        | OldTermStateSemiring.OneOf tss ->
          Logic.or_ (List.map ~f:tss_to_logic tss)
        | OldTermStateSemiring.Transition (_,_,f,sub_anses) ->
          Logic.and_ (f::(List.map ~f:tss_to_logic sub_anses))
        | OldTermStateSemiring.FinalLogic (f,tss) ->
          Logic.band f (tss_to_logic tss)
      end
    in
    tss_to_logic tss

  let remove_transition a label constrt sources st =
    remove_transition
      (Configuration.make
         ~label
         ~sources
         ~constrt)
      st
      a

  let count = ref 0
  let all_constraints_for_state
      (a:t)
    : State.t -> Logic.t =
    let sm = StateMap.empty () in
    let find_req s = StateMap.find_default ~default:Logic.false_ s sm in
    let process_transition
        (_:Symbol.t)
        (ins:State.t list)
        (constrt:Logic.t)
        (out:State.t)
      : (Symbol.t * State.t list * Logic.t * State.t) list =
      count := !count+1;
      let old_reqs =
        find_req
          out
      in
      let new_reqs =
        Logic.and_
          (constrt
           ::(List.map ~f:find_req ins))
      in
      let updated_reqs = Logic.or_ [old_reqs;new_reqs] in
      if not (Logic.valid (Logic.implies updated_reqs old_reqs)) then
        let triggered_transitions = transitions_from a out in
        StateMap.add
          out
          updated_reqs
          sm;
        triggered_transitions
      else
        []
    in
    let rec transition_loop
        (stacked_ts:(Symbol.t * State.t list * Logic.t * State.t) list)
      : unit =
      begin match stacked_ts with
        | (i,ins,l,out)::t ->
          let triggereds =
            process_transition
              i
              ins
              l
              out
          in
          transition_loop
            (t@triggereds)
        | [] -> ()
      end
    in
    let zeroary_transitions =
      List.filter
        ~f:(fun t -> Int.equal (Symbol.arity (CoreAndMore.fst_quad t)) 0)
        (transitions a)
    in
    count := 0;
    transition_loop
      zeroary_transitions;
    fun st ->
      StateMap.find_default
        ~default:Logic.false_
        st
        sm

  let get_all_constraints
      (a:t)
    : (State.t * Logic.t) list =
    let states = states a in
    let logic_mapping = all_constraints_for_state a in
    List.map
      ~f:(fun fs -> (fs,Logic.band (logic_mapping fs) (State.logic_rep fs)))
      states

  let get_finals_and_constraints
      (a:t)
    : (State.t * Logic.t) list =
    let final_states = final_states a in
    let logic_mapping = all_constraints_for_state a in
    List.map
      ~f:(fun fs -> (fs,Logic.band (logic_mapping fs) (State.logic_rep fs)))
      final_states
end
