import AbiModel.Decode

/-!
Boolean checks used by the `#guard` batteries (`AbiModel/Sanity.lean`,
`AbiTest/Enum.lean`). Kept free of `#guard`s so that the natively compiled
`AbiTest` library can import it: loading `Sanity`'s native code crashes the
elaborator.
-/

namespace AbiModel

/-- Wire-level round-trip check: re-encoding the decode of an encoding reproduces
    the wire. `#guard` fails at elaboration if the Bool is false, so each line is a
    machine-checked round-trip at that concrete type/value (no `sorry`). -/
def rt (t : Ty) (v : Value t) : Bool := encode t (decode t (encode t v)) == encode t v

/-- Exact-wire check against the std `abi_encode` layout (word-indexed). -/
def wireIs (t : Ty) (v : Value t) (expected : List Nat) : Bool :=
  (encode t v).map (·.toNat) == expected

end AbiModel
