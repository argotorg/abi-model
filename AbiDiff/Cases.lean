import AbiDiff.Solc

/-! Hand-picked cases covering each layout rule of the model. -/

namespace AbiDiff
open AbiModel

def fixedCases : List Case := [
  -- static
  ⟨.word, (42 : Word)⟩,
  ⟨.bool, true⟩,
  ⟨.pair .word .word, ((3, 4) : Word × Word)⟩,
  ⟨.pair .unit .word, (((), 3) : Unit × Word)⟩,
  ⟨.sum .word .word, (Sum.inl 5 : Word ⊕ Word)⟩,
  ⟨.sum .word .word, (Sum.inr 7 : Word ⊕ Word)⟩,
  -- static sum whose branches have different head widths (padding)
  ⟨.sum (.pair .word .word) .word, (Sum.inr 7 : (Word × Word) ⊕ Word)⟩,
  ⟨.sum (.sum .word .bool) .unit, (Sum.inl (Sum.inr true) : (Word ⊕ Bool) ⊕ Unit)⟩,
  -- dynamic arrays
  ⟨.array .word, ([10, 20, 30] : List Word)⟩,
  ⟨.array .word, ([] : List Word)⟩,
  ⟨.pair .word (.array .word), ((9, [5, 6]) : Word × List Word)⟩,
  ⟨.pair (.array .word) .word, (([5, 6], 9) : List Word × Word)⟩,
  -- ABITuple wrapping a dynamic value, at head offset 0 and not 0
  ⟨.tup (.array .word), ([4, 5] : List Word)⟩,
  ⟨.pair .word (.tup (.array .word)), ((9, [5, 6]) : Word × List Word)⟩,
  ⟨.tup (.pair .word (.array .word)), ((1, [2]) : Word × List Word)⟩,
  -- dynamic sums
  ⟨.sum .word (.array .word), (Sum.inl 1 : Word ⊕ List Word)⟩,
  ⟨.sum .word (.array .word), (Sum.inr [1, 2, 3] : Word ⊕ List Word)⟩,
  ⟨.sum (.pair .word (.array .word)) (.array .word),
    (Sum.inl (5, [7]) : (Word × List Word) ⊕ List Word)⟩,
  ⟨.sum (.pair .word (.array .word)) (.array .word),
    (Sum.inr [7] : (Word × List Word) ⊕ List Word)⟩,
  ⟨.pair .word (.sum .word (.array .word)), ((9, Sum.inr [1, 2]) : Word × (Word ⊕ List Word))⟩
]

end AbiDiff
