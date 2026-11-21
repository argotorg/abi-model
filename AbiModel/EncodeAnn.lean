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
  | .enum n t cs, v, tb =>
      if isStatic t && isStaticC cs then
        ⟨.tag, armTag n t cs v⟩ :: (annArmHead sc t cs v tb
          ++ List.replicate (max (headWords t) (maxArmC cs) - armWords t cs v) ⟨.pad, 0⟩)
      else [⟨.off, natW (sc * tb)⟩]
  termination_by t => (sizeOf t, 1, 0)

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
      ⟨.len, natW xs.length⟩ :: (annHeadSeq sc a xs (xs.length * elemWords a) ++ annTailSeq sc a xs)
  | .enum n t cs, v =>
      if isStatic t && isStaticC cs then []
      else
        ⟨.tag, armTag n t cs v⟩ :: (annArmHead sc t cs v (1 + max (headWords t) (maxArmC cs))
          ++ List.replicate (max (headWords t) (maxArmC cs) - armWords t cs v) ⟨.pad, 0⟩
          ++ annArmTail sc t cs v)
  termination_by t => (sizeOf t, 1, 0)

/-- `armHead` with roles and scaled offsets. -/
def annArmHead (sc : Nat) : (t : Ty) → (cs : Ctors) → Value t ⊕ ValueC cs → Nat → List Cell
  | t, _, .inl x, tb => annHead sc t x tb
  | _, .cons _ u cs, .inr y, tb => annArmHead sc u cs y tb
  | _, .last _ u, .inr y, tb => annHead sc u y tb
  termination_by t cs => (sizeOf t + sizeOf cs, 0, 0)
  decreasing_by all_goals simp_wf; all_goals first | omega | (have := Ctors.sizeOf_pos ‹Ctors›; omega)

/-- `armTail` with roles and scaled offsets. -/
def annArmTail (sc : Nat) : (t : Ty) → (cs : Ctors) → Value t ⊕ ValueC cs → List Cell
  | t, _, .inl x => annTail sc t x
  | _, .cons _ u cs, .inr y => annArmTail sc u cs y
  | _, .last _ u, .inr y => annTail sc u y
  termination_by t cs => (sizeOf t + sizeOf cs, 0, 0)
  decreasing_by all_goals simp_wf; all_goals first | omega | (have := Ctors.sizeOf_pos ‹Ctors›; omega)

/-- `encElemHead` with roles and scaled offsets. -/
def annElemHead (sc : Nat) : (a : Ty) → Value a → Nat → List Cell
  | .pair a b, x, tb =>
      if isStatic a && isStatic b then annHead sc (.pair a b) x tb else [⟨.off, natW (sc * tb)⟩]
  | t, x, tb => annHead sc t x tb
  termination_by a => (sizeOf a, 1, 1)

/-- `encElemTail` with roles and scaled offsets. -/
def annElemTail (sc : Nat) : (a : Ty) → Value a → List Cell
  | .pair a b, x =>
      if isStatic a && isStatic b then annTail sc (.pair a b) x
      else annHead sc (.pair a b) x (headWords a + headWords b) ++ annTail sc (.pair a b) x
  | t, x => annTail sc t x
  termination_by a => (sizeOf a, 1, 1)

def annHeadSeq (sc : Nat) : (a : Ty) → List (Value a) → Nat → List Cell
  | _, [], _ => []
  | a, x :: xs, tb => annElemHead sc a x tb ++ annHeadSeq sc a xs (tb + (encElemTail a x).length)
  termination_by a xs => (sizeOf a, 2, xs.length)

def annTailSeq (sc : Nat) : (a : Ty) → List (Value a) → List Cell
  | _, [] => []
  | a, x :: xs => annElemTail sc a x ++ annTailSeq sc a xs
  termination_by a xs => (sizeOf a, 2, xs.length)

end

/-- Labelled encoding with offsets scaled by `sc`. -/
def encodeAnn (sc : Nat) (t : Ty) (v : Value t) : List Cell :=
  annHead sc t v (headWords t) ++ annTail sc t v

/-- The byte-level wire (offsets in bytes), as solcore-rs's `abi_encode` lays it out. -/
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
  | .enum n t cs, v, tb => by
      by_cases hs : (isStatic t && isStaticC cs) = true
      · simp [annHead, encHead, hs, annArmHead_one t cs v tb]
      · simp only [Bool.not_eq_true] at hs
        simp [annHead, encHead, hs]
  termination_by t => (sizeOf t, 1, 0)

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
  | .enum n t cs, v => by
      by_cases hs : (isStatic t && isStaticC cs) = true
      · simp [annTail, encTail, hs]
      · simp only [Bool.not_eq_true] at hs
        simp [annTail, encTail, hs, annArmHead_one t cs v, annArmTail_one t cs v]
  termination_by t => (sizeOf t, 1, 0)

theorem annArmHead_one : (t : Ty) → (cs : Ctors) → (v : Value t ⊕ ValueC cs) → (tb : Nat) →
    (annArmHead 1 t cs v tb).map (·.val) = armHead t cs v tb
  | t, _, .inl x, tb => by simp only [annArmHead, armHead]; exact annHead_one t x tb
  | _, .cons _ u cs, .inr y, tb => by
      rw [annArmHead.eq_2, armHead.eq_2]; exact annArmHead_one u cs y tb
  | _, .last _ u, .inr y, tb => by
      rw [annArmHead.eq_3, armHead.eq_3]; exact annHead_one u y tb
  termination_by t cs => (sizeOf t + sizeOf cs, 0, 0)
  decreasing_by all_goals simp_wf; all_goals first | omega | (have := Ctors.sizeOf_pos ‹Ctors›; omega)

theorem annArmTail_one : (t : Ty) → (cs : Ctors) → (v : Value t ⊕ ValueC cs) →
    (annArmTail 1 t cs v).map (·.val) = armTail t cs v
  | t, _, .inl x => by simp only [annArmTail, armTail]; exact annTail_one t x
  | _, .cons _ u cs, .inr y => by
      rw [annArmTail.eq_2, armTail.eq_2]; exact annArmTail_one u cs y
  | _, .last _ u, .inr y => by
      rw [annArmTail.eq_3, armTail.eq_3]; exact annTail_one u y
  termination_by t cs => (sizeOf t + sizeOf cs, 0, 0)
  decreasing_by all_goals simp_wf; all_goals first | omega | (have := Ctors.sizeOf_pos ‹Ctors›; omega)

theorem annElemHead_one : (a : Ty) → (x : Value a) → (tb : Nat) →
    (annElemHead 1 a x tb).map (·.val) = encElemHead a x tb
  | .pair a b, x, tb => by
      by_cases h : (isStatic a && isStatic b) = true
      · simp only [annElemHead, encElemHead, h, if_true]; exact annHead_one (.pair a b) x tb
      · simp [annElemHead, encElemHead, h]
  | .unit, x, tb => by simp only [annElemHead, encElemHead]; exact annHead_one _ x tb
  | .word, x, tb => by simp only [annElemHead, encElemHead]; exact annHead_one _ x tb
  | .bool, x, tb => by simp only [annElemHead, encElemHead]; exact annHead_one _ x tb
  | .sum a b, x, tb => by simp only [annElemHead, encElemHead]; exact annHead_one _ x tb
  | .tup a, x, tb => by simp only [annElemHead, encElemHead]; exact annHead_one _ x tb
  | .array a, x, tb => by simp only [annElemHead, encElemHead]; exact annHead_one _ x tb
  | .enum n t cs, x, tb => by simp only [annElemHead, encElemHead]; exact annHead_one _ x tb
  termination_by a => (sizeOf a, 1, 1)

theorem annElemTail_one : (a : Ty) → (x : Value a) →
    (annElemTail 1 a x).map (·.val) = encElemTail a x
  | .pair a b, x => by
      by_cases h : (isStatic a && isStatic b) = true
      · simp only [annElemTail, encElemTail, h, if_true]; exact annTail_one (.pair a b) x
      · simp only [annElemTail, encElemTail, h, Bool.false_eq_true, if_false, List.map_append]
        rw [annHead_one, annTail_one]
  | .unit, x => by simp only [annElemTail, encElemTail]; exact annTail_one _ x
  | .word, x => by simp only [annElemTail, encElemTail]; exact annTail_one _ x
  | .bool, x => by simp only [annElemTail, encElemTail]; exact annTail_one _ x
  | .sum a b, x => by simp only [annElemTail, encElemTail]; exact annTail_one _ x
  | .tup a, x => by simp only [annElemTail, encElemTail]; exact annTail_one _ x
  | .array a, x => by simp only [annElemTail, encElemTail]; exact annTail_one _ x
  | .enum n t cs, x => by simp only [annElemTail, encElemTail]; exact annTail_one _ x
  termination_by a => (sizeOf a, 1, 1)

theorem annHeadSeq_one : (a : Ty) → (xs : List (Value a)) → (tb : Nat) →
    (annHeadSeq 1 a xs tb).map (·.val) = encHeadSeq a xs tb
  | _, [], _ => by simp [annHeadSeq, encHeadSeq]
  | a, x :: xs, tb => by
      simp [annHeadSeq, encHeadSeq, annElemHead_one a, annHeadSeq_one a xs]
  termination_by a xs => (sizeOf a, 2, xs.length)

theorem annTailSeq_one : (a : Ty) → (xs : List (Value a)) →
    (annTailSeq 1 a xs).map (·.val) = encTailSeq a xs
  | _, [] => by simp [annTailSeq, encTailSeq]
  | a, x :: xs => by
      simp [annTailSeq, encTailSeq, annElemTail_one a, annTailSeq_one a xs]
  termination_by a xs => (sizeOf a, 2, xs.length)

end

/-- With unit scale and the labels dropped, the annotated encoder *is* the model. -/
theorem encodeAnn_one (t : Ty) (v : Value t) : (encodeAnn 1 t v).map (·.val) = encode t v := by
  simp [encodeAnn, encode, annHead_one, annTail_one]

/-! ### Scaling

An encoding at scale `sc` differs from the unit-scale one only in its offset
words, each multiplied by `sc` (modulo `2^256`, like the std's `word`
arithmetic). So the byte-level wire is the word-indexed model with offsets in
bytes (`encodeBytes_eq`), of the same length (`encodeBytes_length`).
-/

/-- Multiply an offset cell by `sc`; other cells are unchanged. -/
def Cell.scale (sc : Nat) (c : Cell) : Cell :=
  if c.role = .off then ⟨.off, natW (sc * c.val.toNat)⟩ else c

@[simp] theorem Cell.scale_off (sc tb : Nat) :
    Cell.scale sc ⟨.off, natW tb⟩ = ⟨.off, natW (sc * tb)⟩ := by
  simp only [Cell.scale, if_true, natW, Cell.mk.injEq, true_and]
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_ofNat, Nat.mul_mod]

@[simp] theorem Cell.scale_data (sc : Nat) (w : Word) : Cell.scale sc ⟨.data, w⟩ = ⟨.data, w⟩ := by
  simp [Cell.scale]
@[simp] theorem Cell.scale_tag (sc : Nat) (w : Word) : Cell.scale sc ⟨.tag, w⟩ = ⟨.tag, w⟩ := by
  simp [Cell.scale]
@[simp] theorem Cell.scale_len (sc : Nat) (w : Word) : Cell.scale sc ⟨.len, w⟩ = ⟨.len, w⟩ := by
  simp [Cell.scale]
@[simp] theorem Cell.scale_pad (sc : Nat) (w : Word) : Cell.scale sc ⟨.pad, w⟩ = ⟨.pad, w⟩ := by
  simp [Cell.scale]

mutual

theorem annHead_scale (sc : Nat) : (t : Ty) → (v : Value t) → (tb : Nat) →
    annHead sc t v tb = (annHead 1 t v tb).map (Cell.scale sc)
  | .unit, _, _ => by simp [annHead]
  | .word, _, _ => by simp [annHead]
  | .bool, _, _ => by simp [annHead]
  | .pair a b, v, tb => by
      simp [annHead, annHead_scale sc a, annHead_scale sc b]
  | .sum a b, v, tb => by
      cases ha : isStatic a <;> cases hb : isStatic b <;> cases v <;>
        simp [annHead, ha, hb, annHead_scale sc a, annHead_scale sc b]
  | .tup a, v, tb => by
      by_cases h : isStatic a = true <;> simp_all [annHead, annHead_scale sc a]
  | .array _, _, _ => by simp [annHead]
  | .enum n t cs, v, tb => by
      by_cases hs : (isStatic t && isStaticC cs) = true
      · simp [annHead, hs, annArmHead_scale sc t cs v tb]
      · simp only [Bool.not_eq_true] at hs
        simp [annHead, hs]
  termination_by t => (sizeOf t, 1, 0)

theorem annTail_scale (sc : Nat) : (t : Ty) → (v : Value t) →
    annTail sc t v = (annTail 1 t v).map (Cell.scale sc)
  | .unit, _ => by simp [annTail]
  | .word, _ => by simp [annTail]
  | .bool, _ => by simp [annTail]
  | .pair a b, v => by simp [annTail, annTail_scale sc a, annTail_scale sc b]
  | .sum a b, v => by
      cases ha : isStatic a <;> cases hb : isStatic b <;> cases v <;>
        simp [annTail, ha, hb, annHead_scale sc a, annHead_scale sc b, annTail_scale sc a,
          annTail_scale sc b]
  | .tup a, v => by
      by_cases h : isStatic a = true <;>
        simp_all [annTail, annHead_scale sc a, annTail_scale sc a]
  | .array a, xs => by
      simp [annTail, annHeadSeq_scale sc a, annTailSeq_scale sc a]
  | .enum n t cs, v => by
      by_cases hs : (isStatic t && isStaticC cs) = true
      · simp [annTail, hs]
      · simp only [Bool.not_eq_true] at hs
        simp [annTail, hs, annArmHead_scale sc t cs v, annArmTail_scale sc t cs v]
  termination_by t => (sizeOf t, 1, 0)

theorem annArmHead_scale (sc : Nat) : (t : Ty) → (cs : Ctors) → (v : Value t ⊕ ValueC cs) →
    (tb : Nat) → annArmHead sc t cs v tb = (annArmHead 1 t cs v tb).map (Cell.scale sc)
  | t, _, .inl x, tb => by simp only [annArmHead]; exact annHead_scale sc t x tb
  | _, .cons _ u cs, .inr y, tb => by
      rw [annArmHead.eq_2, annArmHead.eq_2]; exact annArmHead_scale sc u cs y tb
  | _, .last _ u, .inr y, tb => by
      rw [annArmHead.eq_3, annArmHead.eq_3]; exact annHead_scale sc u y tb
  termination_by t cs => (sizeOf t + sizeOf cs, 0, 0)
  decreasing_by all_goals simp_wf; all_goals first | omega | (have := Ctors.sizeOf_pos ‹Ctors›; omega)

theorem annArmTail_scale (sc : Nat) : (t : Ty) → (cs : Ctors) → (v : Value t ⊕ ValueC cs) →
    annArmTail sc t cs v = (annArmTail 1 t cs v).map (Cell.scale sc)
  | t, _, .inl x => by simp only [annArmTail]; exact annTail_scale sc t x
  | _, .cons _ u cs, .inr y => by
      rw [annArmTail.eq_2, annArmTail.eq_2]; exact annArmTail_scale sc u cs y
  | _, .last _ u, .inr y => by
      rw [annArmTail.eq_3, annArmTail.eq_3]; exact annTail_scale sc u y
  termination_by t cs => (sizeOf t + sizeOf cs, 0, 0)
  decreasing_by all_goals simp_wf; all_goals first | omega | (have := Ctors.sizeOf_pos ‹Ctors›; omega)

theorem annElemHead_scale (sc : Nat) : (a : Ty) → (x : Value a) → (tb : Nat) →
    annElemHead sc a x tb = (annElemHead 1 a x tb).map (Cell.scale sc)
  | .pair a b, x, tb => by
      by_cases h : (isStatic a && isStatic b) = true
      · simp only [annElemHead, h, if_true]; exact annHead_scale sc (.pair a b) x tb
      · simp [annElemHead, h]
  | .unit, x, tb => by simp only [annElemHead]; exact annHead_scale sc _ x tb
  | .word, x, tb => by simp only [annElemHead]; exact annHead_scale sc _ x tb
  | .bool, x, tb => by simp only [annElemHead]; exact annHead_scale sc _ x tb
  | .sum a b, x, tb => by simp only [annElemHead]; exact annHead_scale sc _ x tb
  | .tup a, x, tb => by simp only [annElemHead]; exact annHead_scale sc _ x tb
  | .array a, x, tb => by simp only [annElemHead]; exact annHead_scale sc _ x tb
  | .enum n t cs, x, tb => by simp only [annElemHead]; exact annHead_scale sc _ x tb
  termination_by a => (sizeOf a, 1, 1)

theorem annElemTail_scale (sc : Nat) : (a : Ty) → (x : Value a) →
    annElemTail sc a x = (annElemTail 1 a x).map (Cell.scale sc)
  | .pair a b, x => by
      by_cases h : (isStatic a && isStatic b) = true
      · simp only [annElemTail, h, if_true]; exact annTail_scale sc (.pair a b) x
      · simp only [annElemTail, h, Bool.false_eq_true, if_false, List.map_append]
        rw [annHead_scale, annTail_scale]
  | .unit, x => by simp only [annElemTail]; exact annTail_scale sc _ x
  | .word, x => by simp only [annElemTail]; exact annTail_scale sc _ x
  | .bool, x => by simp only [annElemTail]; exact annTail_scale sc _ x
  | .sum a b, x => by simp only [annElemTail]; exact annTail_scale sc _ x
  | .tup a, x => by simp only [annElemTail]; exact annTail_scale sc _ x
  | .array a, x => by simp only [annElemTail]; exact annTail_scale sc _ x
  | .enum n t cs, x => by simp only [annElemTail]; exact annTail_scale sc _ x
  termination_by a => (sizeOf a, 1, 1)

theorem annHeadSeq_scale (sc : Nat) : (a : Ty) → (xs : List (Value a)) → (tb : Nat) →
    annHeadSeq sc a xs tb = (annHeadSeq 1 a xs tb).map (Cell.scale sc)
  | _, [], _ => by simp [annHeadSeq]
  | a, x :: xs, tb => by
      simp [annHeadSeq, annElemHead_scale sc a, annHeadSeq_scale sc a xs]
  termination_by a xs => (sizeOf a, 2, xs.length)

theorem annTailSeq_scale (sc : Nat) : (a : Ty) → (xs : List (Value a)) →
    annTailSeq sc a xs = (annTailSeq 1 a xs).map (Cell.scale sc)
  | _, [] => by simp [annTailSeq]
  | a, x :: xs => by
      simp [annTailSeq, annElemTail_scale sc a, annTailSeq_scale sc a xs]
  termination_by a xs => (sizeOf a, 2, xs.length)

end

theorem encodeAnn_scale (sc : Nat) (t : Ty) (v : Value t) :
    encodeAnn sc t v = (encodeAnn 1 t v).map (Cell.scale sc) := by
  simp [encodeAnn, annHead_scale sc, annTail_scale sc]

/-- The roles of the cells do not depend on the scale. -/
theorem encodeAnn_roles (sc : Nat) (t : Ty) (v : Value t) :
    (encodeAnn sc t v).map (·.role) = (encodeAnn 1 t v).map (·.role) := by
  rw [encodeAnn_scale]
  simp only [List.map_map]
  congr 1
  funext c
  simp only [Function.comp, Cell.scale]
  split <;> simp_all

/-- The byte-level wire has as many words as the model's. -/
theorem encodeBytes_length (t : Ty) (v : Value t) :
    (encodeBytes t v).length = (encode t v).length := by
  rw [← encodeAnn_one, encodeBytes, List.length_map, List.length_map,
    encodeAnn_scale, List.length_map]

/-- The byte-level wire is the model's wire with every offset word `× 32`: the
    `i`-th word is `32 × (encode t v)[i]` where the cell is an offset, and
    `(encode t v)[i]` otherwise. -/
theorem encodeBytes_eq (t : Ty) (v : Value t) :
    encodeBytes t v = (encodeAnn 1 t v).map fun c =>
      if c.role = .off then natW (32 * c.val.toNat) else c.val := by
  rw [encodeBytes, encodeAnn_scale, List.map_map]
  congr 1
  funext c
  simp only [Function.comp, Cell.scale]
  split <;> rfl

end AbiModel
