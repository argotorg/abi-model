import AbiModel.Val

namespace AbiModel

/-- A `Nat` offset, as a 256-bit word. In the std the offset is in bytes; here it
    is in words (bytes = 32 × this). -/
def natW (n : Nat) : Word := BitVec.ofNat 256 n

/-- Padding words after an `inl` branch so both branches of a static sum fill the
    same `max(...)`-wide union. -/
def padL (a b : Ty) : Nat := max (headWords a) (headWords b) - headWords a

/-- Padding after an `inr` branch. -/
def padR (a b : Ty) : Nat := max (headWords a) (headWords b) - headWords b

/-!
Canonical ABI encoder in the head/tail scheme (word-indexed), aligned with the
std `ABIEncode.encodeInto` / `abi_encode` (`std/std.sol:1365,1458`) and
`doc/src/core/abi-encoding-decoding.md`.

`encode t v = encHead t v (headWords t) ++ encTail t v`. The head has fixed width
`headWords t`; a *dynamic* node writes a single offset word into the head pointing
at where its data begins in the shared tail (`tb`). A `pair` lays its components
inline in the head and threads the tail cursor; a dynamic `sum`/`tup`/`array`
places one offset word and puts its `[..]` block in the tail.
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
  termination_by t => (sizeOf t, 0)

def encTail : (t : Ty) → Value t → Wire
  | .unit, _ => []
  | .word, _ => []
  | .bool, _ => []
  | .pair a b, v => encTail a v.1 ++ encTail b v.2
  | .sum a b, v =>
      if isStatic a && isStatic b then []
      else match v with
        | .inl x => (0 : Word) :: (encHead a x (headWords a) ++ encTail a x)
        | .inr y => (1 : Word) :: (encHead b y (headWords b) ++ encTail b y)
  | .tup a, v => if isStatic a then [] else (encHead a v (headWords a) ++ encTail a v)
  | .array a, xs =>
      natW xs.length :: (encHeadSeq a xs (xs.length * headWords a) ++ encTailSeq a xs)
  termination_by t => (sizeOf t, 0)

/-- Element *heads* of an array, threading the tail cursor `tb`. For a static
    element type this is the inline element encoding; for a dynamic one it is the
    per-element offset table. -/
def encHeadSeq : (a : Ty) → List (Value a) → Nat → Wire
  | _, [], _ => []
  | a, x :: xs, tb => encHead a x tb ++ encHeadSeq a xs (tb + (encTail a x).length)
  termination_by a xs => (sizeOf a, xs.length)

/-- Element *tails* of an array (empty when the element type is static). -/
def encTailSeq : (a : Ty) → List (Value a) → Wire
  | _, [] => []
  | a, x :: xs => encTail a x ++ encTailSeq a xs
  termination_by a xs => (sizeOf a, xs.length)

end

/-- Full canonical encoding: head placed first, then the tail. -/
def encode (t : Ty) (v : Value t) : Wire := encHead t v (headWords t) ++ encTail t v

end AbiModel
