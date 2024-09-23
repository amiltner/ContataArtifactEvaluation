open CoreAndMore
open Lang


module SketchVerifier = struct
  module type S = sig
    module L : Language.S
    val satisfies_post_formula :
      context:L.Context.t ->
      cands:(Id.t * L.Expr.t) list ->
      form:UniversalFormula.Make(L).t ->
      (Id.t * L.Value.t) list option
  end
end

module GroundSketchSynthesizer = struct
  module type S = sig
    module L : Language.S
    val solve :
      context:L.Context.t ->
      L.GroundSketch.t ->
      (Id.t * L.Expr.t) list
  end
end

module SketchSynthesizer = struct
  module type S = sig
    module L : Language.S
    val solve :
      context:L.Context.t ->
      sketch:L.Sketch.t ->
      (Id.t * Expr.t) list
  end

  module Make
      (L : Language.S)
      (SV : SketchVerifier.S with module L = L)
      (GSS : GroundSketchSynthesizer.S with module L = L) = struct
    module L = L

    let rec solve_internal
        ~(context:L.Context.t)
        ~(sketch:L.Sketch.t)
        ~(ground_sketches:L.GroundSketch.t)
      : (Id.t * L.Expr.t) list =
      Log.cegis (fun _ -> "Solving Ground Sketches:\n\t" ^
                          Str.global_replace
                            (Str.regexp "\n")
                            "\n\t"
                            (L.GroundSketch.show ground_sketches));
      let cands =
        GSS.solve
          ~context
          ground_sketches
      in
      Log.cegis (fun _ -> "Candidates Found:\n" ^
                          String.concat
                            ~sep:"\n"
                            (List.map
                               ~f:(fun (id,expr) ->
                                   "\tId: " ^ (Id.show id) ^
                                   "\n\tExpr: " ^ (L.Expr.show expr))
                               cands));
      let form_cex_o =
        List.find_map
          ~f:(fun form ->
              let cex_o =
                SV.satisfies_post_formula
                  ~context
                  ~cands
                  ~form
              in
              Option.map ~f:(fun cex -> (form,cex)) cex_o)
          sketch.forms
      in
      begin match form_cex_o with
        | None ->
          cands
        | Some (form,inputs) ->
          Log.cegis (fun _ -> "Counterexample Found:\n\t" ^
                              Str.global_replace
                                (Str.regexp "\n")
                                "\n\t"
                                (String.concat
                                   ~sep:"\n"
                                   (List.map
                                      ~f:(fun (id,value) ->
                                          "Id: " ^ (Id.show id) ^
                                          " Value: " ^ (L.Value.show value))
                                      inputs)));
          Log.cegis (fun _ -> "For Formula:\n\t" ^
                              Str.global_replace
                                (Str.regexp "\n")
                                "\n\t"
                                (L.UniversalFormula.show form));
          let ground_sketches =
            L.GroundSketch.integrate_uf_and_inputs
              ground_sketches
              form
              inputs
          in
          solve_internal
            ~context
            ~sketch
            ~ground_sketches
      end


    let solve
        ~(context:L.Context.t)
        ~(sketch:L.Sketch.t)
      : (Id.t * L.Expr.t) list =
      solve_internal
        ~context
        ~ground_sketches:(L.GroundSketch.from_sketch sketch)
        ~sketch
  end
end

(*module Verifier = struct
  module type S = sig
    val satisfies_post :
      context:Context.t ->
      tin:Type.t ->
      tout:Type.t ->
      cand:Expr.t ->
      checker:(Value.t -> Value.t -> bool) ->
      Value.t option
  end
end

module VerifiedPredicate = struct
  module type S =
  sig
    val synth :
      problem:Problem.t ->
      context:Context.t ->
      tin:Type.t ->
      tout:Type.t ->
      (Value.t -> Value.t -> bool) ->
      Expr.t

  end

  module Make(S : PredicateSynth.S)(V : Verifier.S) : S = struct
    let synth
        ~(problem:Problem.t)
        ~(context:Context.t)
        ~(tin:Type.t)
        ~(tout:Type.t)
        (checker:Value.t -> Value.t -> bool)
      : Expr.t =
      let rec synth_internal
          (sacc:S.t)
          (inputs:Value.t list)
        : Expr.t =
        let (sacc,cand) = S.synth sacc inputs checker in
        Consts.log (fun _ -> "Candidate Found: " ^ (Expr.show cand));
        let cex_o = V.satisfies_post ~context ~tin ~tout ~cand ~checker in
        begin match cex_o with
          | None -> cand
          | Some cex ->
            Consts.log (fun _ -> "CEx Found: " ^ (Value.show cex));
            synth_internal sacc (cex::inputs)
        end
      in
      synth_internal (S.init ~problem ~context ~tin ~tout) []
  end

  module ToIOSynth(VP : Verifier.S -> S) : IOSynth.S = struct
    type t = Problem.t * Context.t * Type.t * Type.t

    let init
        ~(problem:Problem.t)
        ~(context:Context.t)
        ~(tin:Type.t)
        ~(tout:Type.t)
      : t =
      (problem,context,tin,tout)

    let context
        ((_,c,_,_):t)
      : Context.t =
      c

    let tin
        ((_,_,tin,_):t)
      : Type.t =
      tin

    let tout
        ((_,_,_,tout):t)
      : Type.t =
      tout

    let synth
        ((problem,context,tin,tout):t)
        (ioes:(Value.t * Value.t) list)
      : t * Expr.t =
      let inputs = List.map ~f:fst ioes in
      let input_singleton =
        (module struct type t = Value.t list let value = inputs end : InputVerifier.IS)
      in
      let module S = VP(InputVerifier.T(val input_singleton)) in
      let check =
        fun inv outv ->
          begin match List.Assoc.find ~equal:Value.equal ioes inv with
            | Some outv' -> Value.equal outv outv'
            | None -> true
          end
      in
      let e = S.synth ~problem ~context ~tin ~tout check in
      ((problem,context,tin,tout),e)
  end
end

module VerifiedEquiv = struct
  module type S =
  sig
    val synth :
      problem:Problem.t ->
      context:Context.t ->
      tin:Type.t ->
      tout:Type.t ->
      (Value.t -> Value.t) ->
      Expr.t
  end

  module Make(S : IOSynth.S)(V : Verifier.S) : S = struct
    let mk_checker
        (runner:Value.t -> Value.t)
        (vin:Value.t)
        (vout:Value.t)
      : bool =
      let vout_correct = runner vin in
      Value.equal vout vout_correct

    let synth
        ~(problem:Problem.t)
        ~(context:Context.t)
        ~(tin:Type.t)
        ~(tout:Type.t)
        (runner:Value.t -> Value.t)
      : Expr.t =
      let checker = mk_checker runner in
      let rec synth_internal
          (sacc:S.t)
          (ios:(Value.t * Value.t) list)
        : Expr.t =
        let (sacc,cand) =
          Consts.time
            Consts.full_synth_times
            (fun () -> S.synth sacc ios)
        in
        Consts.log (fun _ -> "Candidate Found: " ^ (Expr.show cand));
        let cex_o = V.satisfies_post ~context ~cand ~checker ~tin ~tout in
        begin match cex_o with
          | None -> cand
          | Some cex ->
            Consts.log (fun _ -> "CEx Found: " ^ (Value.show cex));
            Consts.loop_count := !Consts.loop_count+1;
            let cex_out = runner cex in
            synth_internal sacc ((cex,cex_out)::ios)
        end
      in
      synth_internal (S.init ~problem ~context ~tin ~tout) []
  end
  end*)
