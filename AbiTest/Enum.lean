import AbiModel.Check

/-!
Enum checks. Constructor tags are `keccak256("Name(argSigs)")` computed by the FFI
`keccak256`, which only runs as native code, so these `#guard`s live in the
`AbiTest` library (built with `precompileModules := true`, like `AbiTest/Keccak.lean`).
-/

namespace AbiModel

-- tags from solcore's `test/examples/dispatch/abi_sum_roundtrip.json`
#guard ctorTag "L" .word = 0x9579c5ddf61e49d0bf336001c25c13f5689ee1abeee1a378b6bef308961641ec#256
#guard ctorTag "X" .word = 0x337229d96e709f076d800bbc51bd1a1c2d4bef08e1bc014b6824ac7256f23c43#256
#guard ctorTag "P" .word = 0x5e1331e0b0cf9596f31b4ecaa4d4d045bc6de1b91d2401dff29221cab1c175b4#256
#guard ctorTag "Q" .word = 0x5dcad53f88dc9d20c351c1bb58593dde38a673b5308c8751aaeb91edd8c97952#256
-- an enum parameter signs structurally: `rtS2(S2)` with `enum S2 { P(uint256), Q(uint256) }`
-- has selector 0x1def993a
#guard (FFI.keccakString ("rtS2(" ++ sigStr (.enum "P" .word (.last "Q" .word)) ++ ")")) >>> 224
  = 0x1def993a#256

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
#guard ctorTag "C" (.pair .word .word) = FFI.keccakString "C(uint256,uint256)"

/-- Dynamic, three constructors: `enum D3 { A(uint256), B(uint256[]), C(uint256) }`. -/
abbrev D3 : Ty := .enum "A" .word (.cons "B" (.array .word) (.last "C" .word))

-- [offset] in the head; [tag | payload head padded to the flat max | payload tail]
#guard encode D3 (Sum.inr (Sum.inl [8, 9])) = [1, ctorTag "B" (.array .word), 2, 2, 8, 9]
#guard encode D3 (Sum.inr (Sum.inr 4)) = [1, ctorTag "C" .word, 4]
#guard rt D3 (Sum.inr (Sum.inl [8, 9]))
#guard rt D3 (Sum.inl 3)

-- nullary constructor: tag of "None()", unit payload, padded to the widest payload
abbrev Opt : Ty := .enum "None" .unit (.last "Some" .word)
#guard encode Opt (Sum.inl ()) = [FFI.keccakString "None()", 0]
#guard rt Opt (Sum.inl ())

-- the last constructor is the default for an unknown tag (lenient, like solcore)
#guard decode S2 [12345, 8] = (Sum.inr 8 : Value S2)
#guard decode E3 [12345, 5, 6, 0] = (Sum.inr (Sum.inr (5, 6)) : Value E3)

-- enums nested in arrays, pairs and other enums (an enum field signs as its rep)
#guard rt (.array D3) [Sum.inr (Sum.inl [1, 2]), Sum.inl 3, Sum.inr (Sum.inr 4)]
#guard rt (.pair .word D3) (9, Sum.inr (Sum.inl [1]))
#guard rt (.array E3) [Sum.inl 1, Sum.inr (Sum.inr (2, 3))]
#guard rt (.enum "Wrap" S2 (.last "Other" (.array .word))) (Sum.inl (Sum.inr 8))
#guard ctorTag "Wrap" S2 = FFI.keccakString "Wrap(sum(uint256,uint256))"

end AbiModel
