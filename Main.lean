import AbiModel
import AbiModel.Sanity  -- machine-checked #guard battery (round trips, exact wires)
import AbiTest          -- FFI keccak known answers and enum checks (native #guards)

open AbiModel

/-- Wire-level round-trip: re-encoding the decode of an encoding reproduces the
    wire (`Wire = List Word` has `BEq`). Complements the round-trip theorems in
    `AbiModel/Roundtrip.lean` and the `Sanity` `#guard` battery. -/
def check (t : Ty) (v : Value t) : Bool := encode t (decode t (encode t v)) == encode t v

def main : IO UInt32 := do
  let ok : Bool := [
    -- static core
    check (.sum .word .word) (Sum.inr (7 : Word)),
    -- dynamic arrays (head/tail with word offsets, aligned to std)
    check (.array .word) ([10, 20, 30] : List Word),
    check (.array (.array .word)) ([[1], [2, 3], []] : List (List Word)),
    check (.pair .word (.array .word)) ((9, [5, 6]) : Word × List Word),
    -- derived enums: one keccak256("Name(argSigs)") tag word (static and dynamic)
    check S2 (Sum.inr 8),
    check D3 (Sum.inr (Sum.inl [8, 9]))
  ].all id
  IO.println "abi-model (binary inl/inr sums; keccak-tagged enums; dynamic arrays via head/tail word offsets)"
  IO.println "  round-trip theorems (no sorry), in AbiModel/Roundtrip.lean:"
  IO.println "    decode_encode_static  : static types"
  IO.println "    decode_encode_fits    : all types, encoding length < 2^256"
  IO.println "    decode_encode_dynamic : dynamic types, encoding length < 2^256"
  IO.println "    (enum tags via the opaque FFI keccak256; distinct tags assumed in `Fits`)"
  IO.println "  #guard battery (round trips, exact wires): AbiModel/Sanity.lean"
  IO.println "  enum #guards (solcore's tags and rtS2 wire): AbiTest/Enum.lean"
  IO.println "  keccak256 (FFI, OpenSSL known answers): AbiTest/Keccak.lean"
  IO.println s!"  sample re-encodes after decode match wire : {ok}"
  return (bif ok then 0 else 1)
