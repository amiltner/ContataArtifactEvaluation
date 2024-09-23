open CoreAndMore

module Level =
  struct
    type t =
  | CEGIS
  | SKETCH
  | Z3
  | CREATION
[@@deriving ord, show, hash, eq]
end

module Util = LogUtil.Create(Level)

let enable_logger
    (logger:((unit -> string) -> unit) ref)
    (l:Level.t)
  : unit =
  logger := Util.print l

let surround_logger
    (logger:((unit -> string) -> unit) ref)
  : (unit -> string) -> unit =
  fun thunk -> !logger thunk

let cegis_logger : ((unit -> string) -> unit) ref = ref (fun thunk -> ())
let cegis (thunk:unit -> string) : unit = !cegis_logger thunk

let sketch_logger : ((unit -> string) -> unit) ref = ref (fun thunk -> ())
let sketch (thunk:unit -> string) : unit = !sketch_logger thunk

let z3_logger : ((unit -> string) -> unit) ref = ref (fun thunk -> ())
let z3 (thunk:unit -> string) : unit = !z3_logger thunk

let creation_logger : ((unit -> string) -> unit) ref = ref (fun thunk -> ())
let creation (thunk:unit -> string) : unit = !creation_logger thunk

let enable_logging
  (x:Level.t)
  : unit =
  begin match x with
    | CEGIS ->
      enable_logger cegis_logger x
    | SKETCH ->
      enable_logger sketch_logger x
    | Z3 ->
      enable_logger z3_logger x
    | CREATION ->
      enable_logger z3_logger x
  end
