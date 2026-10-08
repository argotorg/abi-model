import AbiModel.Decode

namespace AbiModel

/-- Wire-level round-trip check: re-encoding the decode of an encoding reproduces
    the wire. `#guard` fails at elaboration if the Bool is false, so each line is a
    machine-checked round-trip at that concrete type/value (no `sorry`). -/
def rt (t : Ty) (v : Value t) : Bool := encode t (decode t (encode t v)) == encode t v

-- array of static words
#guard rt (.array .word) ([10,20,30] : List Word)

-- array of arrays (dynamic elements: per-element offset table)
#guard rt (.array (.array .word)) ([[1],[2,3],[]] : List (List Word))

-- array nested on the left of a pair, static field on the right
#guard rt (.pair (.array .word) .word) (([5,6], 9) : List Word × Word)

-- array nested on the right of a pair (offset threading past a static head)
#guard rt (.pair .word (.array .word)) ((9, [5,6]) : Word × List Word)

-- array of static pairs (multi-word inline elements)
#guard rt (.array (.pair .word .word)) ([(1,2),(3,4)] : List (Word × Word))

-- static sum (unchanged core behavior)
#guard rt (.sum .word .word) (Sum.inr 7 : Word ⊕ Word)

-- dynamic sum (a branch is a dynamic array -> single offset word in the head)
#guard rt (.sum .word (.array .word)) (Sum.inr [1,2,3] : Word ⊕ List Word)

-- tup wrapping a dynamic array
#guard rt (.tup (.array .word)) ([4,5] : List Word)

-- array of static sums
#guard rt (.array (.sum .word .word)) ([Sum.inl 1, Sum.inr 2] : List (Word ⊕ Word))

-- array of dynamic sums (offset table over dynamic elements)
#guard rt (.array (.sum .word (.array .word)))
          ([Sum.inl 1, Sum.inr [2,3]] : List (Word ⊕ List Word))

/-- Exact-wire check against the std `abi_encode` layout (word-indexed). -/
def wireIs (t : Ty) (v : Value t) (expected : List Nat) : Bool :=
  (encode t v).map (·.toNat) == expected

-- dynamic sum: branch offsets are relative to the tag word (std `newBase = tail`)
#guard wireIs test1_dyn_sum_ty test1_dyn_sum_val [1, 0, 2, 3, 3, 6, 9, 2, 0, 4, 2, 1, 5, 2, 2, 6]

-- array of arrays: inner offsets relative to the element region
#guard wireIs test2_array_ty test2_array_val [1, 3, 3, 7, 10, 3, 0, 4, 8, 2, 1, 5, 2, 2, 6]

-- dynamic sum with branches of different head widths: the branch head is padded
-- to `max` of both (std `innerHead = 32 + max(headSize f, headSize g)`)
#guard wireIs (.sum (.pair .word (.array .word)) (.array .word))
              (Sum.inr [7] : (Word × List Word) ⊕ List Word) [1, 1, 3, 0, 1, 7]
#guard wireIs (.sum (.pair .word (.array .word)) (.array .word))
              (Sum.inl (5, [7]) : (Word × List Word) ⊕ List Word) [1, 0, 5, 3, 1, 7]
#guard rt (.sum (.pair .word (.array .word)) (.array .word))
          (Sum.inr [7] : (Word × List Word) ⊕ List Word)
#guard rt (.sum (.pair .word (.array .word)) (.array .word))
          (Sum.inl (5, [7]) : (Word × List Word) ⊕ List Word)

-- dynamic sum nested in an array and in a pair (rebasing composes)
#guard rt (.array (.sum (.pair .word (.array .word)) (.array .word)))
          ([Sum.inr [1, 2], Sum.inl (3, [4])] : List ((Word × List Word) ⊕ List Word))
#guard rt (.pair .word (.sum .word (.array .word)))
          ((9, Sum.inr [1, 2]) : Word × (Word ⊕ List Word))

end AbiModel
