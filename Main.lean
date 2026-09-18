import AbiModel

open AbiModel

/-- A concrete round-trip check at the wire level (`Wire = List Word` has `BEq`),
    complementing the machine-checked `decodeAll_encode` theorem in
    `AbiModel/Roundtrip.lean`. -/
def main : IO UInt32 := do
  -- sum(word, word), inr branch: wire is [tag = 1 | 7].
  let t : Ty := .sum .word .word
  let v : Value t := Sum.inr (7 : Word)
  let wire := encode t v
  let ok : Bool :=
    match decodeAll t wire with
    | some v' => encode t v' == wire
    | none => false
  IO.println "abi-model (aligned to doc: binary inl/inr sums)"
  IO.println "  round-trip theorem: AbiModel.decodeAll_encode (no sorry)"
  IO.println s!"  sample re-encode after decode matches wire : {ok}"
  return (bif ok then 0 else 1)
