import AbiModel.EncodeAnn
import AbiModel.Decode

namespace AbiModel

/-!
# The strict decoder

`decStrict` follows solcore-rs's calldata decoder (`f11d56f`) step by step, at
the byte level, including where it reverts. It is the decoder the dispatcher
runs on a public method's arguments (`std/dispatch.sol`, `do_exec`), built from:

- the bounded reader `CalldataWordReader` (`std/std.sol`, `checkReaderRange`):
  `advance(off)` requires `off ≤ end - ptr`, `read` requires 32 bytes left,
  and the end is `calldatasize()`; any failure reverts with
  `ABIInputTruncated()` (`0x08638556`);
- the `ABIDecode` instances of `std/std.sol` (`uint256`, `bool`, `()`, pairs,
  `ABITuple`, `memory<DynArray<t>>`) and `std/ABIGeneric.sol` (`sum`);
- the derived decoder of an enum (`specialize/src/specialize/derived_abi.rs`),
  which compares the tag with each constructor's in order and calls `absurd`
  (an empty revert) when none matches;
- `do_exec`'s check that the calldata holds at least the arguments' head.

Positions are byte positions in the arguments, i.e. the calldata after the
4-byte selector (the reader starts at `calldata(4)`). Offsets read from the
input are arbitrary words: they need not be canonical nor word-aligned; only
the bounds are checked. Padding words and trailing bytes are never checked.

The input is given as words (`Input.words`, big-endian, as the model encodes)
and a byte length (`Input.size`), so that the canonical input is just
`encodeBytes t v` and a truncation is a smaller `size`. Every read is within
`size`, so bytes of `words` past `size` are never looked at.

Array elements follow `ABIElement`: a product element uses `ABITuple`'s layout
(an offset word when dynamic). The array decoder is the eager one of
`memory<DynArray<t>>`, which decodes and checks every element; solcore-rs's
`calldata<array<t>>` (the only array parameter with non-word elements) checks
the head the same way but decodes an element only when it is accessed.
-/

/-- Why solcore-rs's decoder reverts. -/
inductive AbiError where
  /-- `ABIInputTruncated()`: a read or an advance past the end of the input. -/
  | truncated
  /-- `DirtyHigherBitsForBool()`: a `bool` word other than `0` or `1`. -/
  | dirtyBool
  /-- `absurd()`: an enum tag that matches no constructor. -/
  | unknownTag
  deriving Repr, DecidableEq, Inhabited

/-- The revert data solcore-rs returns for an error (hex, without `0x`):
    the 4-byte error selector, or nothing for `absurd`. -/
def AbiError.revertHex : AbiError → String
  | .truncated => "08638556"
  | .dirtyBool => "0557dbbf"
  | .unknownTag => ""

/-- The arguments of a call: big-endian words and the byte length. -/
structure Input where
  words : Wire
  size : Nat

/-- The canonical input for a value: its byte-level encoding, in full. -/
def Input.ofWire (W : Wire) : Input := ⟨W, 32 * W.length⟩

/-- The 32 bytes at byte position `p` (big-endian; reads past `words` give
    zero bytes, but the decoder never reads past `size`). -/
def Input.wordAt (I : Input) (p : Nat) : Word :=
  let q := p / 32
  let r := p % 32
  if r = 0 then rd I.words q
  else (rd I.words q <<< (8 * r)) ||| (rd I.words (q + 1) >>> (8 * (32 - r)))

abbrev Dec := Except AbiError

/-- `WordReader.advance`: from position `p`, `off` bytes further. -/
def Input.adv (I : Input) (p off : Nat) : Dec Nat :=
  if p + off ≤ I.size then pure (p + off) else throw .truncated

/-- `WordReader.read` at position `p`. -/
def Input.read (I : Input) (p : Nat) : Dec Word :=
  if p + 32 ≤ I.size then pure (I.wordAt p) else throw .truncated

/-- `read(advance(rdr, ho))`: the word at `ho` bytes from the reader at `p`. -/
def Input.readAt (I : Input) (p ho : Nat) : Dec Word := do
  I.read (← I.adv p ho)

/-- `2^256 - 1`, the std's `~0`. -/
def maxWord : Nat := 2 ^ 256 - 1

mutual

/-- Decode a value of type `t` whose head is `ho` bytes after the reader at
    position `p` (the std's `ABIDecode.decode(ABIDecoder(rdr), ho)`). -/
def decS : (t : Ty) → Input → Nat → Nat → Dec (Value t)
  | .unit, _, _, _ => pure ()
  | .word, I, p, ho => I.readAt p ho
  | .bool, I, p, ho => do
      let w ← I.readAt p ho
      if w.toNat ≤ 1 then pure (w.toNat == 1) else throw .dirtyBool
  | .pair a b, I, p, ho => do
      let x ← decS a I p ho
      let y ← decS b I p (ho + 32 * headWords a)
      pure (x, y)
  | .sum a b, I, p, ho => do
      -- the sum's start: inline when static, behind an offset when dynamic
      let s ← if isStatic a && isStatic b then I.adv p ho
        else do I.adv p (← I.readAt p ho).toNat
      let tag ← I.read s
      if tag = 0 then return .inl (← decS a I s 32)
      else return .inr (← decS b I s 32)
  | .tup a, I, p, ho =>
      if isStatic a then decS a I p ho
      else do decS a I (← I.adv p (← I.readAt p ho).toNat) 0
  | .array a, I, p, ho => do
      let arr ← I.adv p (← I.readAt p ho).toNat
      let len := (← I.read arr).toNat
      let el ← I.adv arr 32
      -- `checkArrayHead`, then the `length < ~0 / 32` check
      let stride := 32 * elemWords a
      if stride > 0 && len > maxWord / stride then throw .truncated
      let _ ← I.adv el (len * stride)
      if !(len < maxWord / 32) then throw .truncated
      decSeqS a I el len 0
  | .enum n t cs, I, p, ho => do
      -- `abiSumReader`
      let s ← if isStatic t && isStaticC cs then I.adv p ho
        else do I.adv p (← I.readAt p ho).toNat
      decArmS n t cs I s (← I.read s)
  termination_by t => (sizeOf t, 1, 0)

/-- The derived enum decoder: the payload of the constructor whose tag is
    `tag`, at 32 bytes from the enum's start `s`; `absurd` if there is none. -/
def decArmS : (n : String) → (t : Ty) → (cs : Ctors) → Input → Nat → Word →
    Dec (Value t ⊕ ValueC cs)
  | n, t, .cons m u cs, I, s, tag =>
      if tag = ctorTag n t then do return .inl (← decS t I s 32)
      else do return .inr (← decArmS m u cs I s tag)
  | n, t, .last m u, I, s, tag =>
      if tag = ctorTag n t then do return .inl (← decS t I s 32)
      else if tag = ctorTag m u then do return .inr (← decS u I s 32)
      else throw .unknownTag
  termination_by _ t cs => (sizeOf t + sizeOf cs, 0, 0)
  decreasing_by all_goals simp_wf; all_goals first | omega | (have := Ctors.sizeOf_pos ‹Ctors›; omega)

/-- An array element (`ABIElement`): a dynamic product element through its
    offset word, as `ABITuple`'s decoder; any other element in place. -/
def decElemS : (a : Ty) → Input → Nat → Nat → Dec (Value a)
  | .pair a b, I, p, ho =>
      if isStatic a && isStatic b then decS (.pair a b) I p ho
      else do decS (.pair a b) I (← I.adv p (← I.readAt p ho).toNat) 0
  | t, I, p, ho => decS t I p ho
  termination_by a => (sizeOf a, 1, 1)

/-- The elements `i, i+1, …` (`k` of them) of an array whose element region
    starts at `el`; element `i`'s head is at `i × stride` bytes. -/
def decSeqS : (a : Ty) → Input → Nat → Nat → Nat → Dec (List (Value a))
  | _, _, _, 0, _ => pure []
  | a, I, el, k + 1, i => do
      let x ← decElemS a I el (i * (32 * elemWords a))
      let xs ← decSeqS a I el k (i + 1)
      pure (x :: xs)
  termination_by a _ _ k => (sizeOf a, 2, k)

end

/-- Decode a public method's argument of type `t` from the calldata after the
    selector, as `do_exec` does: first check that the head fits, then decode
    from position 0. -/
def decStrict (t : Ty) (I : Input) : Dec (Value t) :=
  if I.size < 32 * headWords t then throw .truncated else decS t I 0 0

/-! ## The lenient decoder at the byte level

`decLax` is `decode` (`AbiModel/Decode.lean`) on the same byte-level input as
`decStrict`: it follows offsets in bytes, reads are total (`Input.wordAt`, zero
past the words), and it never fails: a nonzero bool word is `true`, a nonzero
sum tag is `inr`, and an unknown enum tag selects the last constructor.
`decStrict` is `decLax` with checks added (`decStrict_refines`).
-/

mutual

def decLax : (t : Ty) → Input → Nat → Nat → Value t
  | .unit, _, _, _ => ()
  | .word, I, p, ho => I.wordAt (p + ho)
  | .bool, I, p, ho => I.wordAt (p + ho) != 0
  | .pair a b, I, p, ho => (decLax a I p ho, decLax b I p (ho + 32 * headWords a))
  | .sum a b, I, p, ho =>
      let s := if isStatic a && isStatic b then p + ho else p + (I.wordAt (p + ho)).toNat
      if I.wordAt s = 0 then .inl (decLax a I s 32) else .inr (decLax b I s 32)
  | .tup a, I, p, ho =>
      if isStatic a then decLax a I p ho else decLax a I (p + (I.wordAt (p + ho)).toNat) 0
  | .array a, I, p, ho =>
      let arr := p + (I.wordAt (p + ho)).toNat
      decSeqLax a I (arr + 32) (I.wordAt arr).toNat 0
  | .enum n t cs, I, p, ho =>
      let s := if isStatic t && isStaticC cs then p + ho else p + (I.wordAt (p + ho)).toNat
      decArmLax n t cs I s (I.wordAt s)
  termination_by t => (sizeOf t, 1, 0)

def decArmLax : (n : String) → (t : Ty) → (cs : Ctors) → Input → Nat → Word →
    Value t ⊕ ValueC cs
  | n, t, .cons m u cs, I, s, tag =>
      if tag = ctorTag n t then .inl (decLax t I s 32) else .inr (decArmLax m u cs I s tag)
  | n, t, .last _ u, I, s, tag =>
      if tag = ctorTag n t then .inl (decLax t I s 32) else .inr (decLax u I s 32)
  termination_by _ t cs => (sizeOf t + sizeOf cs, 0, 0)
  decreasing_by all_goals simp_wf; all_goals first | omega | (have := Ctors.sizeOf_pos ‹Ctors›; omega)

def decElemLax : (a : Ty) → Input → Nat → Nat → Value a
  | .pair a b, I, p, ho =>
      if isStatic a && isStatic b then decLax (.pair a b) I p ho
      else decLax (.pair a b) I (p + (I.wordAt (p + ho)).toNat) 0
  | t, I, p, ho => decLax t I p ho
  termination_by a => (sizeOf a, 1, 1)

def decSeqLax : (a : Ty) → Input → Nat → Nat → Nat → List (Value a)
  | _, _, _, 0, _ => []
  | a, I, el, k + 1, i => decElemLax a I el (i * (32 * elemWords a)) :: decSeqLax a I el k (i + 1)
  termination_by a _ _ k => (sizeOf a, 2, k)

end

end AbiModel
