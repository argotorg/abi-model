import AbiModel.Encode

namespace AbiModel

/-- Read the word at absolute index `i` (0 past the end). The std reverts on
    out-of-bounds; here reads are total, which keeps the lenient decoder total. -/
def rd (W : Wire) (i : Nat) : Word := W.getD i 0

/-!
Base-relative canonical decoder, aligned with the std `ABIDecode` / word readers
(`std/std.sol:1524,1679,1757`). `decAt t W base ho` reads the value of type `t`
whose head sits at absolute index `base + ho` in `W`, following offset words into
the shared tail exactly as `abiArrayGet` / the dynamic-sum decoder do. Reads are
total (`rd`), so the decoder is total; it stays *lenient* on tags (any nonzero `sum` tag
word decodes as the right injection, an unknown `enum` tag as its last
constructor, a nonzero bool word as `true`), matching the real decoder.
-/
mutual

def decAt : (t : Ty) → Wire → Nat → Nat → Value t
  | .unit, _, _, _ => ()
  | .word, W, base, ho => rd W (base + ho)
  | .bool, W, base, ho => rd W (base + ho) != 0
  | .pair a b, W, base, ho =>
      (decAt a W base ho, decAt b W base (ho + headWords a))
  | .sum a b, W, base, ho =>
      if isStatic a && isStatic b then
        if rd W (base + ho) = 0 then Sum.inl (decAt a W base (ho + 1))
        else Sum.inr (decAt b W base (ho + 1))
      else
        let o := (rd W (base + ho)).toNat
        -- rebase at the tag word (the std's `sumRdr`); the branch head is at 1
        if rd W (base + o) = 0 then Sum.inl (decAt a W (base + o) 1)
        else Sum.inr (decAt b W (base + o) 1)
  | .tup a, W, base, ho =>
      if isStatic a then decAt a W base ho
      else decAt a W (base + (rd W (base + ho)).toNat) 0
  | .array a, W, base, ho =>
      let o := (rd W (base + ho)).toNat
      let len := (rd W (base + o)).toNat
      decSeq a W (base + o + 1) len 0
  | .enum n t cs, W, base, ho =>
      if isStatic t && isStaticC cs then decArm n t cs W base (ho + 1) (rd W (base + ho))
      else
        let o := (rd W (base + ho)).toNat
        -- rebase at the tag word (the std's `abiSumReader`); the payload head is at 1
        decArm n t cs W (base + o) 1 (rd W (base + o))
  termination_by t => (sizeOf t, 1, 0)

/-- Dispatch on an enum's tag word, decoding the selected constructor's payload
    head at `base + ho`. Like the derived solcore decoder
    (`DeriveGeneric.buildABIDecodeSum`), each constructor but the last is matched
    by its `ctorTag` in order and the last is the default (lenient on unknown tags). -/
def decArm : (n : String) → (t : Ty) → (cs : Ctors) → Wire → Nat → Nat → Word →
    Value t ⊕ ValueC cs
  | n, t, .cons m u cs, W, base, ho, tag =>
      if tag = ctorTag n t then Sum.inl (decAt t W base ho)
      else Sum.inr (decArm m u cs W base ho tag)
  | n, t, .last _ u, W, base, ho, tag =>
      if tag = ctorTag n t then Sum.inl (decAt t W base ho)
      else Sum.inr (decAt u W base ho)
  termination_by _ t cs => (sizeOf t + sizeOf cs, 0, 0)
  decreasing_by all_goals simp_wf; all_goals first | omega | (have := Ctors.sizeOf_pos ‹Ctors›; omega)

/-- Decode `n` array elements from an element region starting at `region`.
    Element `i`'s head sits at `region + i * headWords a` (inline for a static
    element type; an offset word into the element's own tail for a dynamic one,
    which `decAt` then follows). -/
def decSeq : (a : Ty) → Wire → Nat → Nat → Nat → List (Value a)
  | _, _, _, 0, _ => []
  | a, W, region, k + 1, i => decAt a W region (i * headWords a) :: decSeq a W region k (i + 1)
  termination_by a _ _ n => (sizeOf a, 2, n)

end

/-- Top-level decode: the value's region starts at index 0. -/
def decode (t : Ty) (w : Wire) : Value t := decAt t w 0 0

/-- Option-valued wrapper, for the retraction theorem's shape. Total (`some _`),
    since reads are total. -/
def decodeAll (t : Ty) (w : Wire) : Option (Value t) := some (decode t w)

end AbiModel
