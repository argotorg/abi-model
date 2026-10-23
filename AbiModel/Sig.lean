import AbiModel.Ty
import AbiModel.FFI.Keccak

namespace AbiModel

/-!
ABI signature strings, aligned with the `SigString` instances in
`std/dispatch.sol`, and the per-constructor enum tags built from them
(`DeriveGeneric.tagE`: `keccakLit("Name(" + sigStr(rep) + ")")`).

`word` stands for `uint256`. An enum signs as its SOP rep (the `Generic` default
instance), i.e. structurally as nested `sum(...)`, never by its name. solcore has
no `SigString` for `ABITuple`, so `tup` signs as its contents; and only
`calldata<array<t>>` signs as `t[]`.
-/
mutual

def sigStr : Ty → String
  | .unit => ""
  | .word => "uint256"
  | .bool => "bool"
  | .pair a b => sigStr a ++ "," ++ sigStr b
  | .sum a b => "sum(" ++ sigStr a ++ "," ++ sigStr b ++ ")"
  | .tup a => sigStr a
  | .array a => sigStr a ++ "[]"
  | .enum _ t cs => "sum(" ++ sigStr t ++ "," ++ sigStrC cs ++ ")"

/-- Signature of the rep of the remaining constructors. -/
def sigStrC : Ctors → String
  | .last _ t => sigStr t
  | .cons _ t cs => "sum(" ++ sigStr t ++ "," ++ sigStrC cs ++ ")"

end

/-- Wire tag of the enum constructor `name` with payload (rep) `t`, via the FFI
    `keccak256` (`AbiModel/FFI/Keccak.lean`). The FFI function is `opaque`, so
    proofs treat tags as uninterpreted words (see `Fits` in `Roundtrip.lean`), and
    evaluating a tag needs native code (tests: `AbiTest/Enum.lean`). -/
def ctorTag (name : String) (t : Ty) : Word :=
  FFI.keccakString (name ++ "(" ++ sigStr t ++ ")")

/-- The wire tags of the remaining constructors of an enum, in order. -/
def tagsC : Ctors → List Word
  | .last m u => [ctorTag m u]
  | .cons m u cs => ctorTag m u :: tagsC cs

end AbiModel
