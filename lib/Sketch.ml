open CoreAndMore
open Lang

module Make(L:Language.S) = struct
  module L = L
  module UF = UniversalFormula.Make(L)

  type t =
    {
      holes     : (Id.t * (L.Type.t * L.Type.t * Id.t list)) list        ;
      forms     : UF.t list                            ;
      predicate : Id.t -> L.Value.t -> L.Value.t -> bool                 ;
    }
  [@@deriving show]

  let make
      ~(holes:(Id.t * (L.Type.t * L.Type.t * Id.t list)) list)
      ~(forms:UF.t list)
      ~(predicate:Id.t -> L.Value.t -> L.Value.t -> bool)
    : t =
    {
      holes     ;
      forms     ;
      predicate ;
    }
end

type t =
  {
    holes     : (Id.t * (Type.t * Type.t * Id.t list)) list        ;
    forms     : UniversalFormula.t list                            ;
    predicate : Id.t -> Value.t -> Value.t -> bool                 ;
  }
[@@deriving show]

let make
    ~(holes:(Id.t * (Type.t * Type.t * Id.t list)) list)
    ~(forms:UniversalFormula.t list)
    ~(predicate:Id.t -> Value.t -> Value.t -> bool)
  : t =
  {
    holes     ;
    forms     ;
    predicate ;
  }
