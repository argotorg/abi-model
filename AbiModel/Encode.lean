import AbiModel.Val
import AbiModel.Sig

namespace AbiModel

/-- A `Nat` offset, as a 256-bit word. In the std the offset is in bytes; here it
    is in words (bytes = 32 × this). -/
def natW (n : Nat) : Word := BitVec.ofNat 256 n

/-- Padding words after an `inl` branch so both branches of a static sum fill the
    same `max(...)`-wide union. -/
def padL (a b : Ty) : Nat := max (headWords a) (headWords b) - headWords a

/-- Padding after an `inr` branch. -/
def padR (a b : Ty) : Nat := max (headWords a) (headWords b) - headWords b

/-- Tag word of the selected constructor of `enum n t cs`. -/
def armTag : (n : String) → (t : Ty) → (cs : Ctors) → Value t ⊕ ValueC cs → Word
  | n, t, _, .inl _ => ctorTag n t
  | _, _, .cons m u cs, .inr y => armTag m u cs y
  | _, _, .last m u, .inr _ => ctorTag m u

/-- Head width of the selected constructor's payload. -/
def armWords : (t : Ty) → (cs : Ctors) → Value t ⊕ ValueC cs → Nat
  | t, _, .inl _ => headWords t
  | _, .cons _ u cs, .inr y => armWords u cs y
  | _, .last _ u, .inr _ => headWords u

/-!
Canonical ABI encoder in the head/tail scheme (word-indexed), aligned with the
std `ABIEncode.encodeInto` / `abi_encode` (`std/std.sol:1365,1458`) and
`doc/src/core/abi-encoding-decoding.md`.

`encode t v = encHead t v (headWords t) ++ encTail t v`. The head has fixed width
`headWords t`; a *dynamic* node writes a single offset word into the head pointing
at where its data begins in the shared tail (`tb`). A `pair` lays its components
inline in the head and threads the tail cursor; a dynamic `sum`/`tup`/`array`
places one offset word and puts its `[..]` block in the tail.

A dynamic sum's tail block mirrors `ABIGeneric.sol`'s `encodeInto`: it is
`[tag | branch head | padding | branch tail]`, where the branch head is padded to
the widest branch (`max (headWords a) (headWords b)`) and the branch's own offsets
are relative to the *tag word* (the std's `newBase = tail`, branch at offset 32).

An `enum` (a derived multi-constructor type) mirrors the derived `ABIEncode`
(`DeriveGeneric.buildABIEncodeSum` → `encodeVariant`): the same static/dynamic
layout, but a single `ctorTag` word (`keccak256("Name(argSigs)")`) for the whole
enum instead of one `0`/`1` word per level of its rep. A static enum is padded
with zeros to the rep's (nested) `headWords`; a dynamic enum's tail block reserves
the flat `1 + max` of the payload heads (`_innerHead`). solcore leaves those
padding words unwritten; the model writes zeros.
-/
mutual

def encHead : (t : Ty) → Value t → Nat → Wire
  | .unit, _, _ => []
  | .word, w, _ => [w]
  | .bool, b, _ => [bif b then 1 else 0]
  | .pair a b, v, tb =>
      encHead a v.1 tb ++ encHead b v.2 (tb + (encTail a v.1).length)
  | .sum a b, v, tb =>
      if isStatic a && isStatic b then
        match v with
        | .inl x => (0 : Word) :: (encHead a x tb ++ List.replicate (padL a b) (0 : Word))
        | .inr y => (1 : Word) :: (encHead b y tb ++ List.replicate (padR a b) (0 : Word))
      else [natW tb]
  | .tup a, v, tb => if isStatic a then encHead a v tb else [natW tb]
  | .array _, _, tb => [natW tb]
  | .enum n t cs, v, tb =>
      if isStatic t && isStaticC cs then
        armTag n t cs v :: (armHead t cs v tb
          ++ List.replicate (max (headWords t) (headWordsC cs) - armWords t cs v) (0 : Word))
      else [natW tb]
  termination_by t => (sizeOf t, 1, 0)

def encTail : (t : Ty) → Value t → Wire
  | .unit, _ => []
  | .word, _ => []
  | .bool, _ => []
  | .pair a b, v => encTail a v.1 ++ encTail b v.2
  | .sum a b, v =>
      if isStatic a && isStatic b then []
      else match v with
        | .inl x =>
            (0 : Word) :: (encHead a x (1 + max (headWords a) (headWords b))
              ++ List.replicate (padL a b) (0 : Word) ++ encTail a x)
        | .inr y =>
            (1 : Word) :: (encHead b y (1 + max (headWords a) (headWords b))
              ++ List.replicate (padR a b) (0 : Word) ++ encTail b y)
  | .tup a, v => if isStatic a then [] else (encHead a v (headWords a) ++ encTail a v)
  | .array a, xs =>
      natW xs.length :: (encHeadSeq a xs (xs.length * headWords a) ++ encTailSeq a xs)
  | .enum n t cs, v =>
      if isStatic t && isStaticC cs then []
      else
        armTag n t cs v :: (armHead t cs v (1 + max (headWords t) (maxArmC cs))
          ++ List.replicate (max (headWords t) (maxArmC cs) - armWords t cs v) (0 : Word)
          ++ armTail t cs v)
  termination_by t => (sizeOf t, 1, 0)

/-- Head of the selected constructor's payload of an enum (no tag word). -/
def armHead : (t : Ty) → (cs : Ctors) → Value t ⊕ ValueC cs → Nat → Wire
  | t, _, .inl x, tb => encHead t x tb
  | _, .cons _ u cs, .inr y, tb => armHead u cs y tb
  | _, .last _ u, .inr y, tb => encHead u y tb
  termination_by t cs => (sizeOf t + sizeOf cs, 0, 0)
  decreasing_by all_goals simp_wf; all_goals first | omega | (have := Ctors.sizeOf_pos ‹Ctors›; omega)

/-- Tail of the selected constructor's payload of an enum. -/
def armTail : (t : Ty) → (cs : Ctors) → Value t ⊕ ValueC cs → Wire
  | t, _, .inl x => encTail t x
  | _, .cons _ u cs, .inr y => armTail u cs y
  | _, .last _ u, .inr y => encTail u y
  termination_by t cs => (sizeOf t + sizeOf cs, 0, 0)
  decreasing_by all_goals simp_wf; all_goals first | omega | (have := Ctors.sizeOf_pos ‹Ctors›; omega)

/-- Element *heads* of an array, threading the tail cursor `tb`. For a static
    element type this is the inline element encoding; for a dynamic one it is the
    per-element offset table. -/
def encHeadSeq : (a : Ty) → List (Value a) → Nat → Wire
  | _, [], _ => []
  | a, x :: xs, tb => encHead a x tb ++ encHeadSeq a xs (tb + (encTail a x).length)
  termination_by a xs => (sizeOf a, 2, xs.length)

/-- Element *tails* of an array (empty when the element type is static). -/
def encTailSeq : (a : Ty) → List (Value a) → Wire
  | _, [] => []
  | a, x :: xs => encTail a x ++ encTailSeq a xs
  termination_by a xs => (sizeOf a, 2, xs.length)

end

/-- Full canonical encoding: head placed first, then the tail. -/
def encode (t : Ty) (v : Value t) : Wire := encHead t v (headWords t) ++ encTail t v

def test1_dyn_sum_ty : Ty := Ty.sum (Ty.array (Ty.array Ty.word)) (Ty.array Ty.word)
def test1_dyn_sum_val : Value test1_dyn_sum_ty := .inl [[natW 0, natW 4], [natW 1, natW 5], [natW 2, natW 6]]
#eval encode test1_dyn_sum_ty test1_dyn_sum_val

-- expected output (std `abi_encode`, word-indexed; offsets are 0-based and
-- relative to the enclosing region's base, never absolute):
-- [1 (offset to sum body, rel. to start), 0 (inl), 2 (offset to outer array, rel. to tag word),
--  3 (length of outer array), 3, 6, 9 (offsets to inner arrays, rel. to the element region),
--  2 (length of first inner array), 0, 4, 2 (length of second inner array), 1, 5,
--  2 (length of third inner array), 2, 6]
-- [1, 0, 2, 3, 3, 6, 9, 2, 0, 4, 2, 1, 5, 2, 2, 6]

-- expected output: [1, 3, 3, 7, 10, 3, 0, 4, 8, 2, 1, 5, 2, 2, 6]
def test2_array_ty : Ty := Ty.array (Ty.array Ty.word)
def test2_array_val : Value test2_array_ty :=[[natW 0, natW 4, natW 8], [natW 1, natW 5], [natW 2, natW 6]]
#eval encode test2_array_ty test2_array_val

end AbiModel
