import AbiModel.Encode

namespace AbiModel

/-- What a word of the encoding stands for. Only used to explain divergences in
    the differential-test report; it carries no semantic weight. -/
inductive Role where
  | data | tag | len | off | pad
  deriving Repr, DecidableEq, Inhabited

def Role.name : Role → String
  | .data => "data" | .tag => "tag" | .len => "length" | .off => "offset" | .pad => "padding"

/-- One encoded word together with its role. -/
structure Cell where
  role : Role
  val  : Word
  deriving Repr, DecidableEq, Inhabited

/-!
`encHead`/`encTail` with every word labelled by its `Role`, and every offset
multiplied by `sc`. With `sc = 1` this is the word-indexed model (`encodeAnn_one`);
with `sc = 32` it is the byte-level wire the EVM produces (`encodeBytes`). Lengths
are element counts and are never scaled.
-/
mutual

def annHead (sc : Nat) : (t : Ty) → Value t → Nat → List Cell
  | .unit, _, _ => []
  | .word, w, _ => [⟨.data, w⟩]
  | .bool, b, _ => [⟨.data, bif b then 1 else 0⟩]
  | .pair a b, v, tb =>
      annHead sc a v.1 tb ++ annHead sc b v.2 (tb + (encTail a v.1).length)
  | .sum a b, v, tb =>
      if isStatic a && isStatic b then
        match v with
        | .inl x => ⟨.tag, 0⟩ :: (annHead sc a x tb ++ List.replicate (padL a b) ⟨.pad, 0⟩)
        | .inr y => ⟨.tag, 1⟩ :: (annHead sc b y tb ++ List.replicate (padR a b) ⟨.pad, 0⟩)
      else [⟨.off, natW (sc * tb)⟩]
  | .tup a, v, tb => if isStatic a then annHead sc a v tb else [⟨.off, natW (sc * tb)⟩]
  | .array _, _, tb => [⟨.off, natW (sc * tb)⟩]
  termination_by t => (sizeOf t, 0)

def annTail (sc : Nat) : (t : Ty) → Value t → List Cell
  | .unit, _ => []
  | .word, _ => []
  | .bool, _ => []
  | .pair a b, v => annTail sc a v.1 ++ annTail sc b v.2
  | .sum a b, v =>
      if isStatic a && isStatic b then []
      else match v with
        | .inl x =>
            ⟨.tag, 0⟩ :: (annHead sc a x (1 + max (headWords a) (headWords b))
              ++ List.replicate (padL a b) ⟨.pad, 0⟩ ++ annTail sc a x)
        | .inr y =>
            ⟨.tag, 1⟩ :: (annHead sc b y (1 + max (headWords a) (headWords b))
              ++ List.replicate (padR a b) ⟨.pad, 0⟩ ++ annTail sc b y)
  | .tup a, v => if isStatic a then [] else (annHead sc a v (headWords a) ++ annTail sc a v)
  | .array a, xs =>
      ⟨.len, natW xs.length⟩ :: (annHeadSeq sc a xs (xs.length * headWords a) ++ annTailSeq sc a xs)
  termination_by t => (sizeOf t, 0)

def annHeadSeq (sc : Nat) : (a : Ty) → List (Value a) → Nat → List Cell
  | _, [], _ => []
  | a, x :: xs, tb => annHead sc a x tb ++ annHeadSeq sc a xs (tb + (encTail a x).length)
  termination_by a xs => (sizeOf a, xs.length)

def annTailSeq (sc : Nat) : (a : Ty) → List (Value a) → List Cell
  | _, [] => []
  | a, x :: xs => annTail sc a x ++ annTailSeq sc a xs
  termination_by a xs => (sizeOf a, xs.length)

end

/-- Labelled encoding with offsets scaled by `sc`. -/
def encodeAnn (sc : Nat) (t : Ty) (v : Value t) : List Cell :=
  annHead sc t v (headWords t) ++ annTail sc t v

/-- The byte-level wire (offsets in bytes), as Solcore's `abi_encode` lays it out. -/
def encodeBytes (t : Ty) (v : Value t) : Wire := (encodeAnn 32 t v).map (·.val)

end AbiModel

namespace AbiModel

mutual

theorem annHead_one : (t : Ty) → (v : Value t) → (tb : Nat) →
    (annHead 1 t v tb).map (·.val) = encHead t v tb
  | .unit, _, _ => by simp [annHead, encHead]
  | .word, _, _ => by simp [annHead, encHead]
  | .bool, _, _ => by simp [annHead, encHead]
  | .pair a b, v, tb => by
      simp [annHead, encHead, annHead_one a, annHead_one b]
  | .sum a b, v, tb => by
      cases ha : isStatic a <;> cases hb : isStatic b <;> cases v <;>
        simp [annHead, encHead, ha, hb, annHead_one a, annHead_one b]
  | .tup a, v, tb => by
      by_cases h : isStatic a = true <;> simp_all [annHead, encHead, annHead_one a]
  | .array _, _, _ => by simp [annHead, encHead]
  termination_by t => (sizeOf t, 0)

theorem annTail_one : (t : Ty) → (v : Value t) →
    (annTail 1 t v).map (·.val) = encTail t v
  | .unit, _ => by simp [annTail, encTail]
  | .word, _ => by simp [annTail, encTail]
  | .bool, _ => by simp [annTail, encTail]
  | .pair a b, v => by simp [annTail, encTail, annTail_one a, annTail_one b]
  | .sum a b, v => by
      cases ha : isStatic a <;> cases hb : isStatic b <;> cases v <;>
        simp [annTail, encTail, ha, hb, annHead_one a, annHead_one b, annTail_one a,
          annTail_one b]
  | .tup a, v => by
      by_cases h : isStatic a = true <;>
        simp_all [annTail, encTail, annHead_one a, annTail_one a]
  | .array a, xs => by
      simp [annTail, encTail, annHeadSeq_one a, annTailSeq_one a]
  termination_by t => (sizeOf t, 0)

theorem annHeadSeq_one : (a : Ty) → (xs : List (Value a)) → (tb : Nat) →
    (annHeadSeq 1 a xs tb).map (·.val) = encHeadSeq a xs tb
  | _, [], _ => by simp [annHeadSeq, encHeadSeq]
  | a, x :: xs, tb => by
      simp [annHeadSeq, encHeadSeq, annHead_one a, annHeadSeq_one a xs]
  termination_by a xs => (sizeOf a, xs.length)

theorem annTailSeq_one : (a : Ty) → (xs : List (Value a)) →
    (annTailSeq 1 a xs).map (·.val) = encTailSeq a xs
  | _, [] => by simp [annTailSeq, encTailSeq]
  | a, x :: xs => by
      simp [annTailSeq, encTailSeq, annTail_one a, annTailSeq_one a xs]
  termination_by a xs => (sizeOf a, xs.length)

end

/-- With unit scale and the labels dropped, the annotated encoder *is* the model. -/
theorem encodeAnn_one (t : Ty) (v : Value t) : (encodeAnn 1 t v).map (·.val) = encode t v := by
  simp [encodeAnn, encode, annHead_one, annTail_one]

end AbiModel
