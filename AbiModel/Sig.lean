import AbiModel.Ty
import AbiModel.Keccak

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

/-- Wire tag of the enum constructor `name` with payload (rep) `t`. -/
def ctorTag (name : String) (t : Ty) : Word :=
  keccakWord (name ++ "(" ++ sigStr t ++ ")")

/-- The wire tags of the remaining constructors of an enum, in order. -/
def tagsC : Ctors → List Word
  | .last m u => [ctorTag m u]
  | .cons m u cs => ctorTag m u :: tagsC cs

-- tags from solcore's `test/examples/dispatch/abi_sum_roundtrip.json`
#guard ctorTag "L" .word = 0x9579c5ddf61e49d0bf336001c25c13f5689ee1abeee1a378b6bef308961641ec#256
#guard ctorTag "X" .word = 0x337229d96e709f076d800bbc51bd1a1c2d4bef08e1bc014b6824ac7256f23c43#256
#guard ctorTag "P" .word = 0x5e1331e0b0cf9596f31b4ecaa4d4d045bc6de1b91d2401dff29221cab1c175b4#256
#guard ctorTag "Q" .word = 0x5dcad53f88dc9d20c351c1bb58593dde38a673b5308c8751aaeb91edd8c97952#256
-- an enum parameter signs structurally: `rtS2(S2)` with `enum S2 { P(uint256), Q(uint256) }`
-- has selector 0x1def993a
#guard (keccakWord ("rtS2(" ++ sigStr (.enum "P" .word (.last "Q" .word)) ++ ")")) >>> 224
  = 0x1def993a#256

end AbiModel
