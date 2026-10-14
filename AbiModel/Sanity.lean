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

/-! ### Derived enums: one `keccak256("Name(argSigs)")` tag word -/

/-- `enum S2 { P(uint256), Q(uint256) }` (solcore `abi_sum_roundtrip.sol`). -/
abbrev S2 : Ty := .enum "P" .word (.last "Q" .word)

-- exact wire of solcore's `rtS2(P(9))` / `rtS2(Q(8))` (static: inline [tag][field])
#guard wireIs S2 (Sum.inl 9)
  [0x5e1331e0b0cf9596f31b4ecaa4d4d045bc6de1b91d2401dff29221cab1c175b4, 9]
#guard wireIs S2 (Sum.inr 8)
  [0x5dcad53f88dc9d20c351c1bb58593dde38a673b5308c8751aaeb91edd8c97952, 8]
#guard rt S2 (Sum.inr 8)

/-- Static, three constructors: `enum E3 { A(uint256), B(uint256), C(uint256, uint256) }`. -/
abbrev E3 : Ty := .enum "A" .word (.cons "B" .word (.last "C" (.pair .word .word)))

-- one tag word, but the rep's nested head width 1 + max(1, 1 + max(1, 2)) = 4
#guard headWords E3 = 4
#guard encode E3 (Sum.inr (Sum.inr (5, 6))) =
  [ctorTag "C" (.pair .word .word), 5, 6, 0]
#guard encode E3 (Sum.inl 7) = [ctorTag "A" .word, 7, 0, 0]
#guard rt E3 (Sum.inr (Sum.inl 7))
#guard rt E3 (Sum.inr (Sum.inr (5, 6)))

-- the signature of a multi-field constructor is comma-joined: "C(uint256,uint256)"
#guard ctorTag "C" (.pair .word .word) = keccakWord "C(uint256,uint256)"

/-- Dynamic, three constructors: `enum D3 { A(uint256), B(uint256[]), C(uint256) }`. -/
abbrev D3 : Ty := .enum "A" .word (.cons "B" (.array .word) (.last "C" .word))

-- [offset] in the head; [tag | payload head padded to the flat max | payload tail]
#guard encode D3 (Sum.inr (Sum.inl [8, 9])) = [1, ctorTag "B" (.array .word), 2, 2, 8, 9]
#guard encode D3 (Sum.inr (Sum.inr 4)) = [1, ctorTag "C" .word, 4]
#guard rt D3 (Sum.inr (Sum.inl [8, 9]))
#guard rt D3 (Sum.inl 3)

-- nullary constructor: tag of "None()", unit payload, padded to the widest payload
abbrev Opt : Ty := .enum "None" .unit (.last "Some" .word)
#guard encode Opt (Sum.inl ()) = [keccakWord "None()", 0]
#guard rt Opt (Sum.inl ())

-- the last constructor is the default for an unknown tag (lenient, like solcore)
#guard decode S2 [12345, 8] = (Sum.inr 8 : Value S2)
#guard decode E3 [12345, 5, 6, 0] = (Sum.inr (Sum.inr (5, 6)) : Value E3)

-- enums nested in arrays, pairs and other enums (an enum field signs as its rep)
#guard rt (.array D3) [Sum.inr (Sum.inl [1, 2]), Sum.inl 3, Sum.inr (Sum.inr 4)]
#guard rt (.pair .word D3) (9, Sum.inr (Sum.inl [1]))
#guard rt (.array E3) [Sum.inl 1, Sum.inr (Sum.inr (2, 3))]
#guard rt (.enum "Wrap" S2 (.last "Other" (.array .word))) (Sum.inl (Sum.inr 8))
#guard ctorTag "Wrap" S2 = keccakWord "Wrap(sum(uint256,uint256))"

end AbiModel
