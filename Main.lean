import AbiModel
import AbiModel.Sanity  -- machine-checked #guard round-trip battery (incl. dynamic arrays)

open AbiModel

/-- Wire-level round-trip: re-encoding the decode of an encoding reproduces the
    wire (`Wire = List Word` has `BEq`). Complements the machine-checked
    `decodeAll_encode_static` theorem and the `Sanity` `#guard` battery. -/
def check (t : Ty) (v : Value t) : Bool := encode t (decode t (encode t v)) == encode t v

def main : IO UInt32 := do
  let ok : Bool := [
    -- static core
    check (.sum .word .word) (Sum.inr (7 : Word)),
    -- dynamic arrays (head/tail with word offsets, aligned to std)
    check (.array .word) ([10, 20, 30] : List Word),
    check (.array (.array .word)) ([[1], [2, 3], []] : List (List Word)),
    check (.pair .word (.array .word)) ((9, [5, 6]) : Word × List Word)
  ].all id
  IO.println "abi-model (binary inl/inr sums; dynamic arrays via head/tail word offsets)"
  IO.println "  static round-trip: theorem AbiModel.decodeAll_encode_static (no sorry)"
  IO.println "  dynamic arrays: machine-checked #guard battery in AbiModel/Sanity.lean"
  IO.println "  keccak256 (FFI): #guard known-answer tests in AbiTest/Keccak.lean"
  IO.println s!"  sample re-encodes after decode match wire : {ok}"
  return (bif ok then 0 else 1)
