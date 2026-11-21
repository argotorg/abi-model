import AbiModel.Sig

/-!
# The external ABI boundary

Which model types solcore-rs accepts as the type of a public method's
parameter (and return value), and the signature it hashes into the selector
(`hir-ty/src/contract/abi.rs`, `signature_type_string` and `abi_type_of`, at
`f11d56f`). The encoding and decoding theorems hold for every `Ty`; this is the
fragment where they describe a contract's calldata and return data.

- `uint256` and `bool`; arrays only as `memory<DynArray<uint256>>` (the std's
  memory arrays need `Typedef<word>` elements);
- products, flattened into one tuple, whose members are not `()`;
- derived enums, whose payloads may hold sums and `()` but no `ABITuple`, and
  arrays only of `uint256`;
- not `()`, sums or `ABITuple` (solcore-rs has no external ABI for them).

A product signs as the tuple of its flattened members, e.g.
`(uint256,bool,uint256[])`; an enum signs as its generic representation, which
is the model's `sigStr`, e.g. `enum E { A(uint256), B(bool, uint256), C }` as
`sum(uint256,sum(bool,uint256,))`.
-/

namespace AbiModel

mutual

/-- Whether solcore-rs accepts the type at its ABI boundary. -/
def isExternal : Ty → Bool
  | .word | .bool => true
  | .array .word => true
  | .pair a b => isExtMember a && isExtMember b
  | .enum _ t cs => isPayload t && isPayloadC cs
  | _ => false

/-- A member of an external product: not `()`; nested products are flattened. -/
def isExtMember : Ty → Bool
  | .unit => false
  | .pair a b => isExtMember a && isExtMember b
  | t => isExternal t

/-- A type an enum's payload may hold: its derived ABI needs every part to
    have std ABI instances. -/
def isPayload : Ty → Bool
  | .unit | .word | .bool => true
  | .pair a b | .sum a b => isPayload a && isPayload b
  | .tup _ => false
  | .array .word => true
  | .array _ => false
  | .enum _ t cs => isPayload t && isPayloadC cs

def isPayloadC : Ctors → Bool
  | .last _ u => isPayload u
  | .cons _ u cs => isPayload u && isPayloadC cs

end

/-- The flattened members of an external product. -/
def extMembers : Ty → List Ty
  | .pair a b => extMembers a ++ extMembers b
  | t => [t]

/-- The signature of an external type, as solcore-rs hashes it into a selector:
    a product is the tuple of its flattened members, anything else its `sigStr`. -/
def extSig : Ty → String
  | .pair a b => "(" ++ ",".intercalate ((extMembers (.pair a b)).map sigStr) ++ ")"
  | t => sigStr t

/-- The selector of a public method `name(x: t)`. -/
def extSelector (name : String) (t : Ty) : BitVec 32 := FFI.selector s!"{name}({extSig t})"

#guard isExternal (.pair .word (.pair .bool (.array .word)))
#guard extSig (.pair .word (.pair .bool (.array .word))) == "(uint256,bool,uint256[])"
#guard !isExternal (.pair .unit .word)
#guard !isExternal (.sum .word .word)
#guard !isExternal (.tup .word)
#guard !isExternal (.array (.array .word))
#guard isExternal (.enum "A" .word (.cons "B" (.pair .bool .word) (.last "C" .unit)))
#guard extSig (.enum "A" .word (.cons "B" (.pair .bool .word) (.last "C" .unit))) ==
  "sum(uint256,sum(bool,uint256,))"
#guard extSig (.enum "A" (.sum .word .bool) (.last "B" (.enum "P" .word (.last "Q" .unit)))) ==
  "sum(sum(uint256,bool),sum(uint256,))"
#guard !isExternal (.enum "A" (.tup .word) (.last "B" .word))

end AbiModel
