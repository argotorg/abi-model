import AbiModel.Check
import AbiModel.EncodeAnn

namespace AbiModel

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

-- Enum checks evaluate constructor tags, i.e. the FFI `keccak256`, so they live in
-- the natively compiled `AbiTest` library: see `AbiTest/Enum.lean`.

end AbiModel

namespace AbiModel

/-- Byte-level wire (offsets × 32), as `abi_encode` returns it. -/
def bytesIs (t : Ty) (v : Value t) (expected : List Nat) : Bool :=
  (encodeBytes t v).map (·.toNat) == expected

-- static product: same as `encPoint(3,4)` in solcore's abi_encode_adt.json
#guard bytesIs (.pair .word .word) ((3, 4) : Word × Word) [3, 4]
-- offsets become byte offsets, lengths stay counts
#guard bytesIs (.pair .word (.array .word)) ((9, [5, 6]) : Word × List Word) [9, 0x40, 2, 5, 6]
#guard bytesIs (.pair .word (.tup (.array .word))) ((9, [5, 6]) : Word × List Word)
  [9, 0x40, 0x20, 2, 5, 6]
#guard bytesIs test1_dyn_sum_ty test1_dyn_sum_val
  [0x20, 0, 0x40, 3, 0x60, 0xc0, 0x120, 2, 0, 4, 2, 1, 5, 2, 2, 6]

end AbiModel
