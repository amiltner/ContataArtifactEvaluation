open CoreAndMore
open Contata
open Lang

let rec import_imports
    (acc:Problem.t_unprocessed)
  : Problem.t_unprocessed =
  begin match Problem.extract_file acc with
    | None -> acc
    | Some (fname,acc) ->
      let (news,newd) =
        ParserContainer.import_decls_start (SimpleFile.read_from_file ~fname)
      in
      let news = Problem.update_import_base news fname in
      import_imports
        (Problem.merge_unprocessed
           acc
           (news,newd))
  end

let handle_log
    (log:string)
  : unit =
  let level =
    begin match log with
      | "cegis" -> Log.Level.CEGIS
      | "sketch" -> Log.Level.SKETCH
      | "z3" -> Log.Level.Z3
      | _ -> failwith "Invalid log level provided"
    end
  in
  Log.enable_logging level

let handle_logs
    (logs:string list)
  : unit =
  List.iter
    ~f:handle_log
    logs

module SillyOld = SketchFTASynthesizer
module AlternatingSkGr = ContataLangFTASynthesizer.S
module CTASkGr = SketchFTASynthesizer.Make(ContataLang)(ContataLangFTASynthesizer.ContataFormulaExtractor)(ContataLangFTASynthesizer.AutomatonCreator)
module AngelicSkGr = Angelic_synthesizer.AngelicSketchFTASynthesizer
module SkV = EnumerativeVerifier.T
module BL = ContataLang
module Sk = Synthesizers.SketchSynthesizer.Make(BL)(SkV)(CTASkGr)
module AngelicSk = Synthesizers.SketchSynthesizer.Make(BL)(SkV)(AngelicSkGr)
module SimpleSk = Synthesizers.SketchSynthesizer.Make(BL)(SkV)(SimpleSketchFTASynthesizer)

let synthesize_satisfying_postcondition
    ~(problem:Problem.t)
    ~(context:Context.t)
    ~(use_angelic:bool)
    ~(use_simple:bool)
  : (Id.t * Expr.t) list =
  let input_types i =
    fst3
      (List.Assoc.find_exn
         ~equal:Id.equal
         problem.synth_targets
         i)
  in
  let (predicate,forms) = Spec.to_pred_and_tests ~context ~input_types problem.specs in
  let sketch =
    Sketch.make
      ~forms
      ~predicate
      ~holes:problem.synth_targets
  in
  if use_angelic then
    AngelicSk.solve
      ~context
      ~sketch
  else if use_simple then
    SimpleSk.solve
      ~context
      ~sketch
  else
    Sk.solve
      ~context
      ~sketch

let synthesize_solution
    ~(fname:string)
    ~(use_simple:bool)
    ~(use_angelic:bool)
    ~(logs:string list)
    ~(no_experiments:bool)
    ~(print_times:bool)
  : unit =
  handle_logs logs;
  let p_unprocessed =
    ParserContainer.unprocessed_problem
      ((CoreAndMore.SimpleFile.read_from_file ~fname))
  in
  let p_unprocessed = Problem.update_all_import_bases p_unprocessed fname in
  let p_unprocessed = import_imports p_unprocessed in
  let problem = Problem.process p_unprocessed in
  let solns =
    let context = Problem.extract_context problem in
    synthesize_satisfying_postcondition
      ~use_angelic
      ~use_simple
      ~problem
      ~context
  in
  let e_str =
    (String.concat ~sep:"\n"
       (List.map
          ~f:(fun (i,e) -> (Id.show i) ^ " := " ^ (Expr.show e))
          solns))
  in
  if no_experiments then
    begin
      print_endline e_str;
      print_endline "@";
      print_endline (Float.to_string (Consts.total Consts.isect_times));
      print_endline "@";
      print_endline (Float.to_string (Consts.max Consts.isect_times));
      print_endline "@";
      print_endline (Float.to_string (Consts.total Consts.minify_times));
      print_endline "@";
      print_endline (Float.to_string (Consts.max Consts.minify_times));
      print_endline "@";
      print_endline (Float.to_string (Consts.total Consts.min_elt_times));
      print_endline "@";
      print_endline (Float.to_string (Consts.max Consts.min_elt_times));
      print_endline "@";
      print_endline (Float.to_string (Consts.total Consts.initial_creation_times));
      print_endline "@";
      print_endline (Float.to_string (Consts.max Consts.initial_creation_times));
      print_endline "@";
      print_endline (Float.to_string (Consts.total Consts.accepts_term_times));
      print_endline "@";
      print_endline (Float.to_string (Consts.max Consts.accepts_term_times));
      print_endline "@";
      print_endline (Int.to_string (!Consts.loop_count));
      print_endline "@";
      print_endline (Float.to_string (Consts.total Consts.full_synth_times));
      print_endline "@";
      print_endline (Float.to_string (Consts.max Consts.full_synth_times));
      print_endline "@";
      print_endline (Float.to_string (Consts.total Consts.z3_times));
      print_endline "@";
      print_endline (Float.to_string (Consts.max Consts.z3_times));
    end
  else
    begin
      print_endline e_str;
      if print_times then
        begin
          print_endline ("Total Intersection Time: " ^ (Float.to_string (Consts.total Consts.isect_times)));
          print_endline ("Max Intersection Time: " ^ (Float.to_string (Consts.max Consts.isect_times)));
          print_endline ("Total Minify Time: " ^ (Float.to_string (Consts.total Consts.minify_times)));
          print_endline ("Max Minify Time: " ^ (Float.to_string (Consts.max Consts.minify_times)));
          print_endline ("Total Min-elt Time: " ^ (Float.to_string (Consts.total Consts.min_elt_times)));
          print_endline ("Max Min-elt Time: " ^ (Float.to_string (Consts.max Consts.min_elt_times)));
          print_endline ("Total Initial Creation Time: " ^ (Float.to_string (Consts.total Consts.initial_creation_times)));
          print_endline ("Max Initial Creation Time: " ^ (Float.to_string (Consts.max Consts.initial_creation_times)));
          print_endline ("Total Accepts Term Time: " ^ (Float.to_string (Consts.total Consts.accepts_term_times)));
          print_endline ("Max Accepts Term Time: " ^ (Float.to_string (Consts.max Consts.accepts_term_times)));
          print_endline ("Total Copy Time: " ^ (Float.to_string (Consts.total Consts.copy_times)));
          print_endline ("Max Copy Time: " ^ (Float.to_string (Consts.max Consts.copy_times)));
        end
    end

let handle_inputs
    ~(fname:string)
    ~(use_simple:bool)
    ~(use_angelic:bool)
    ~(logs:string list)
    ~(no_experiments:bool)
    ~(print_times:bool)
    ~(use_random:bool)
  : unit =
  Consts.use_random := use_random;
  synthesize_solution
    ~fname
    ~use_simple
    ~use_angelic
    ~logs
    ~no_experiments
    ~print_times

open CoreAndMore.Command.Let_syntax
let param =
  CoreAndMore.Command.basic ~summary:"..."
    [%map_open
      let input_spec  = anon ("input_spec" %: string)
      and use_simple   = flag "use-simple" no_arg ~doc:"Solve using the simple synthesis engine"
      and logs =
        flag "log" (listed string) ~doc:"log at level (permitted: cegis, sketch, z3)"
      and use_angelic   = flag "use-angelic" no_arg ~doc:"Solve using the angelic synthesis approach"
      and print_times   = flag "print-times" no_arg ~doc:"print the times to run various components"
      and no_experiments   = flag "no-experiments" no_arg ~doc:"do not print experiment timing"
      and use_random   = flag "use-random" no_arg ~doc:"print timbuk to vata mapping"
      in
      let no_experiments = not no_experiments in
      fun () ->
        handle_inputs
          ~fname:input_spec
          ~use_simple
          ~use_angelic
          ~logs
          ~print_times
          ~no_experiments
          ~use_random
    ]

let () =
  Command_unix.run
    param
