import AbiModel.DecodeStrict
import AbiModel.Check

/-!
Checks of the strict decoder `decStrict`, on canonical input and on the inputs
solcore-rs rejects or accepts although they are not canonical. Enum cases
evaluate tags (the FFI), hence this file lives in `AbiTest`.
-/

namespace AbiModel

/-- `decStrict` on `I` succeeds with a value whose encoding is `expected`. -/
def okWith (t : Ty) (I : Input) (expected : Wire) : Bool :=
  match decStrict t I with
  | .ok v => encodeBytes t v == expected
  | .error _ => false

/-- `decStrict` on `I` fails with `e`. -/
def failsWith (t : Ty) (I : Input) (e : AbiError) : Bool :=
  match decStrict t I with
  | .ok _ => false
  | .error e' => e' == e

/-- The canonical input of `v` decodes back to `v`. -/
def strictRt (t : Ty) (v : Value t) : Bool :=
  okWith t (.ofWire (encodeBytes t v)) (encodeBytes t v)

abbrev SE3 : Ty := .enum "A" .word (.cons "B" .word (.last "C" (.pair .word .word)))
abbrev SD3 : Ty := .enum "A" .word (.cons "B" (.array .word) (.last "C" .word))

/-! ### Canonical input -/

#guard strictRt .word 42
#guard strictRt .bool true
#guard strictRt (.pair .word .word) (3, 4)
#guard strictRt (.pair .unit .word) ((), 3)
#guard strictRt (.sum (.pair .word .word) .word) (.inr 7)
#guard strictRt (.array .word) [10, 20, 30]
#guard strictRt (.array .word) []
#guard strictRt (.pair .word (.array .word)) (9, [5, 6])
#guard strictRt (.pair .word (.tup (.array .word))) (9, [5, 6])
#guard strictRt (.sum (.pair .word (.array .word)) (.array .word)) (.inl (5, [7]))
#guard strictRt (.array (.array .word)) [[1, 2], [], [3]]
#guard strictRt SE3 (.inr (.inr (5, 6)))
#guard strictRt SE3 (.inl 7)
#guard strictRt SD3 (.inr (.inl [8, 9]))
#guard strictRt (.array SD3) [.inr (.inl [1, 2]), .inl 3, .inr (.inr 4)]
#guard strictRt (.pair .word (.enum "P" .word (.last "Q" .word))) (9, .inl 3)

#guard strictRt (.array (.pair .word (.array .word))) [(7, [1, 2]), (8, [3])]
#guard strictRt (.array (.pair (.array .word) (.pair .word (.array .word))))
  [([1], (2, [3, 4])), ([], (5, []))]

/-! ### Reverts -/

-- the head must fit (`do_exec`), and every read must be in bounds
#guard failsWith .word ⟨[42], 31⟩ .truncated
#guard failsWith (.pair .word .word) ⟨[3, 4], 63⟩ .truncated
-- an offset past the end
#guard failsWith (.array .word) ⟨[0x40, 1, 5], 96⟩ .truncated
-- the length claims more elements than there are bytes
#guard failsWith (.array .word) ⟨[0x20, 3, 5, 6], 128⟩ .truncated
-- a length whose byte size would wrap a word
#guard failsWith (.array .word) ⟨[0x20, natW (2 ^ 255)], 64⟩ .truncated
-- a dirty bool, also inside a pair after a valid field
#guard failsWith .bool ⟨[2], 32⟩ .dirtyBool
#guard failsWith (.pair .word .bool) ⟨[1, 0xff], 64⟩ .dirtyBool
-- an unknown enum tag reverts (the lenient `decode` takes the last constructor)
#guard failsWith SE3 ⟨[12345, 5, 6], 96⟩ .unknownTag
#guard failsWith SD3 ⟨[0x20, 12345, 0x40, 0], 128⟩ .unknownTag
-- the first error wins: a truncation before the dirty bool
#guard failsWith (.pair (.array .word) .bool) ⟨[0x1000, 2], 64⟩ .truncated

/-! ### Accepted non-canonical input -/

-- any nonzero sum tag is `inr`
#guard okWith (.sum .word .word) ⟨[7, 5], 64⟩ [1, 5]
-- the padding after a short sum branch or enum payload is not checked
#guard okWith (.sum (.pair .word .word) .word) ⟨[1, 7, 99], 96⟩ [1, 7, 0]
#guard okWith SE3 ⟨[ctorTag "A" .word, 7, 99], 96⟩ [ctorTag "A" .word, 7, 0]
-- trailing bytes are ignored
#guard okWith .word ⟨[42, 1, 2], 96⟩ [42]
-- an offset need not point right after the head
#guard okWith (.array .word) ⟨[0x40, 999, 1, 5], 128⟩ [0x20, 1, 5]
-- nor be word-aligned: the array at byte 0x21 (its length word straddles two words)
#guard okWith (.array .word) ⟨[0x21, 0, (1 : Word) <<< 248, (5 : Word) <<< 248], 0x21 + 64⟩
  [0x20, 1, 5]
-- two heads may share a tail
#guard okWith (.pair (.array .word) (.array .word)) ⟨[0x40, 0x40, 1, 5], 128⟩
  [0x40, 0x80, 1, 5, 1, 5]

/-! ### Unaligned reads -/

#guard Input.wordAt ⟨[1, 2], 64⟩ 31 = (1 : Word) <<< 248
#guard Input.wordAt ⟨[1, 2], 64⟩ 32 = 2
#guard Input.wordAt ⟨[0xff, 0], 64⟩ 16 = (0xff : Word) <<< 128

/-! ### The lenient byte-level decoder

Where `decStrict` reverts, `decLax` returns a value with `decode`'s leniency.
-/

/-- `decLax` from the start of `I` gives a value whose encoding is `expected`. -/
def laxGives (t : Ty) (I : Input) (expected : Wire) : Bool :=
  encodeBytes t (decLax t I 0 0) == expected

-- an unknown enum tag: the last constructor
#guard laxGives SE3 ⟨[12345, 5, 6], 96⟩ (encodeBytes SE3 (.inr (.inr (5, 6))))
-- a dirty bool: `true`
#guard laxGives .bool ⟨[2], 32⟩ [1]
-- truncated input: zeros past the end
#guard laxGives (.pair .word .word) ⟨[3], 32⟩ [3, 0]
-- on canonical input it agrees with the strict decoder
#guard laxGives (.pair .word (.array .word)) (.ofWire [9, 0x40, 2, 5, 6]) [9, 0x40, 2, 5, 6]
#guard laxGives SD3 (.ofWire (encodeBytes SD3 (.inr (.inl [8, 9]))))
  (encodeBytes SD3 (.inr (.inl [8, 9])))

end AbiModel
