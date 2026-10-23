import AbiModel.Decode

namespace AbiModel

/-!
`Ty` is mutually inductive with `Ctors`, so the lemmas below recurse on the type
(well-founded on `sizeOf`) instead of using `induction`; each lemma that has to
look inside an enum has an `arm*` companion over the remaining constructors,
mirroring the `arm*` helpers of the encoder.

**Keccak.** Enum tags are `ctorTag n t = FFI.keccakString ("n(" ++ sigStr t ++ ")")`,
where `FFI.keccak256` is an `opaque` `@[extern]` function implemented in C. Proofs
cannot evaluate it and nothing here unfolds `ctorTag`: the theorems hold for
*every* function `ByteArray → ByteArray` the opaque constant might denote. The only
fact about tags they use is the distinct-tags hypothesis in `Fits`, which is an
assumption about the hash's values on the signatures that actually occur (see
`Fits`). No axiom is added: `#print axioms` lists only `propext`,
`Classical.choice` and `Quot.sound`.
-/

/-! ### The selected enum constructor: head width and tag -/

/-- The selected payload head fits the flat widest payload (dynamic layout). -/
theorem armWords_le_maxArm : ∀ (t : Ty) (cs : Ctors) (v : Value t ⊕ ValueC cs),
    armWords t cs v ≤ max (headWords t) (maxArmC cs)
  | _, _, .inl _ => by simp only [armWords]; omega
  | _, .cons _ u cs, .inr y => by
      have := armWords_le_maxArm u cs y
      simp only [armWords, maxArmC]; omega
  | _, .last _ _, .inr _ => by simp only [armWords, maxArmC]; omega
  termination_by _ cs => sizeOf cs

/-- The selected payload head fits the rep's (nested) width (static layout). -/
theorem armWords_le_headWordsC : ∀ (t : Ty) (cs : Ctors) (v : Value t ⊕ ValueC cs),
    isStaticC cs = true → armWords t cs v ≤ max (headWords t) (headWordsC cs)
  | _, _, .inl _, _ => by simp only [armWords]; omega
  | _, .cons _ u cs, .inr y, h => by
      have hs : isStatic u = true ∧ isStaticC cs = true := by simpa [isStaticC] using h
      have := armWords_le_headWordsC u cs y hs.2
      simp only [armWords, headWordsC, hs.1, hs.2, Bool.and_self, if_true]; omega
  | _, .last _ _, .inr _, _ => by simp only [armWords, headWordsC]; omega
  termination_by _ cs => sizeOf cs

/-- The written tag is one of the enum's constructor tags. -/
theorem armTag_mem : ∀ (n : String) (t : Ty) (cs : Ctors) (v : Value t ⊕ ValueC cs),
    armTag n t cs v ∈ ctorTag n t :: tagsC cs
  | _, _, _, .inl _ => by simp [armTag]
  | _, _, .cons m u cs, .inr y => by
      have := armTag_mem m u cs y
      simp only [armTag, tagsC]; exact List.mem_cons_of_mem _ this
  | _, _, .last _ _, .inr _ => by simp [armTag, tagsC]
  termination_by _ _ cs => sizeOf cs

/-- A later constructor's tag differs from the first one's, when the tags are distinct. -/
theorem armTag_inr_ne {n : String} {t : Ty} {cs : Ctors} {y : ValueC cs}
    (hnd : (ctorTag n t :: tagsC cs).Nodup) :
    armTag n t cs (Sum.inr y) ≠ ctorTag n t := by
  intro h
  apply (List.nodup_cons.mp hnd).1
  rw [← h]
  cases cs with
  | cons m u cs =>
      have := armTag_mem m u cs y
      simpa only [armTag, tagsC] using this
  | last m u => simp [armTag, tagsC]

/-! ### Heads and tails -/

mutual

/-- The head of any value has exactly `headWords t` words. -/
theorem encHead_length : ∀ (t : Ty) (v : Value t) (tb : Nat),
    (encHead t v tb).length = headWords t
  | .unit => by intro v tb; simp only [encHead, headWords]; rfl
  | .word => by intro v tb; simp only [encHead, headWords]; rfl
  | .bool => by intro v tb; simp only [encHead, headWords]; rfl
  | .pair a b => by
      intro v tb
      simp only [encHead, headWords, List.length_append, encHead_length a, encHead_length b]
  | .sum a b => by
      have iha := encHead_length a
      have ihb := encHead_length b
      intro v tb
      by_cases hs : (isStatic a && isStatic b) = true
      · cases v with
        | inl x => simp [encHead, headWords, hs, iha, padL]; omega
        | inr y => simp [encHead, headWords, hs, ihb, padR]; omega
      · simp only [Bool.not_eq_true] at hs
        cases v with
        | inl x => simp [encHead, headWords, hs]
        | inr y => simp [encHead, headWords, hs]
  | .tup a => by
      intro v tb
      by_cases hs : isStatic a = true
      · simp only [encHead, headWords, hs, if_pos]; exact encHead_length a v tb
      · simp only [Bool.not_eq_true] at hs
        simp only [encHead, headWords]; simp [hs]
  | .array a => by intro v tb; simp only [encHead, headWords]; rfl
  | .enum n t cs => by
      intro v tb
      by_cases hs : (isStatic t && isStaticC cs) = true
      · have hl := armHead_length t cs v tb
        have hle := armWords_le_headWordsC t cs v (by simp only [Bool.and_eq_true] at hs; exact hs.2)
        simp [encHead, headWords, hs, hl]; omega
      · simp only [Bool.not_eq_true] at hs
        simp [encHead, headWords, hs]
  termination_by t => (sizeOf t, 1)

/-- The selected payload head has exactly `armWords` words. -/
theorem armHead_length : ∀ (t : Ty) (cs : Ctors) (v : Value t ⊕ ValueC cs) (tb : Nat),
    (armHead t cs v tb).length = armWords t cs v
  | t, _, .inl x, tb => by simp only [armHead, armWords]; exact encHead_length t x tb
  | _, .cons _ u cs, .inr y, tb => by
      rw [armHead.eq_2]; simp only [armWords]; exact armHead_length u cs y tb
  | _, .last _ u, .inr y, tb => by
      rw [armHead.eq_3]; simp only [armWords]; exact encHead_length u y tb
  termination_by t cs => (sizeOf t + sizeOf cs, 0)
  decreasing_by all_goals simp_wf; all_goals first | omega | (have := Ctors.sizeOf_pos ‹Ctors›; omega)

end

/-- A static type has no tail. -/
theorem encTail_nil_of_static : ∀ (t : Ty) (v : Value t),
    isStatic t = true → encTail t v = []
  | .unit => by intro v _; simp only [encTail]
  | .word => by intro v _; simp only [encTail]
  | .bool => by intro v _; simp only [encTail]
  | .pair a b => by
      intro v h
      simp only [isStatic, Bool.and_eq_true] at h
      simp only [encTail, encTail_nil_of_static a v.1 h.1, encTail_nil_of_static b v.2 h.2,
        List.append_nil]
  | .sum a b => by
      intro v h
      simp only [isStatic] at h
      cases v <;> simp [encTail, h]
  | .tup a => by
      intro v h
      simp only [isStatic] at h
      simp [encTail, h]
  | .array a => by intro v h; simp [isStatic] at h
  | .enum n t cs => by
      intro v h
      simp only [isStatic] at h
      simp [encTail, h]
  termination_by t => sizeOf t

mutual

/-- For a static type the head does not depend on the tail cursor. -/
theorem encHead_static_tb_irrel : ∀ (t : Ty) (v : Value t) (tb tb' : Nat),
    isStatic t = true → encHead t v tb = encHead t v tb'
  | .unit => by intro v tb tb' _; simp [encHead]
  | .word => by intro v tb tb' _; simp [encHead]
  | .bool => by intro v tb tb' _; simp [encHead]
  | .pair a b => by
      intro v tb tb' h
      simp only [isStatic, Bool.and_eq_true] at h
      have hta : encTail a v.1 = [] := encTail_nil_of_static a v.1 h.1
      simp only [encHead, hta, List.length_nil, Nat.add_zero]
      rw [encHead_static_tb_irrel a v.1 tb tb' h.1, encHead_static_tb_irrel b v.2 tb tb' h.2]
  | .sum a b => by
      intro v tb tb' h
      have hs : (isStatic a && isStatic b) = true := by simp only [isStatic] at h; exact h
      simp only [isStatic, Bool.and_eq_true] at h
      cases v with
      | inl x => simp only [encHead, hs, if_true]; rw [encHead_static_tb_irrel a x tb tb' h.1]
      | inr y => simp only [encHead, hs, if_true]; rw [encHead_static_tb_irrel b y tb tb' h.2]
  | .tup a => by
      intro v tb tb' h
      have hs : isStatic a = true := by simp only [isStatic] at h; exact h
      simp only [encHead, hs, if_true]
      exact encHead_static_tb_irrel a v tb tb' hs
  | .array a => by intro v tb tb' h; simp [isStatic] at h
  | .enum n t cs => by
      intro v tb tb' h
      have hs : (isStatic t && isStaticC cs) = true := by simp only [isStatic] at h; exact h
      simp only [isStatic, Bool.and_eq_true] at h
      simp only [encHead, hs, if_true]
      rw [armHead_static_tb_irrel t cs v tb tb' h.1 h.2]
  termination_by t => (sizeOf t, 1)

/-- For a static enum the selected payload head does not depend on the tail cursor. -/
theorem armHead_static_tb_irrel : ∀ (t : Ty) (cs : Ctors) (v : Value t ⊕ ValueC cs)
    (tb tb' : Nat), isStatic t = true → isStaticC cs = true →
    armHead t cs v tb = armHead t cs v tb'
  | t, _, .inl x, tb, tb', ht, _ => by
      simp only [armHead]; exact encHead_static_tb_irrel t x tb tb' ht
  | _, .cons _ u cs, .inr y, tb, tb', _, hcs => by
      have h : isStatic u = true ∧ isStaticC cs = true := by simpa [isStaticC] using hcs
      rw [armHead.eq_2, armHead.eq_2]; exact armHead_static_tb_irrel u cs y tb tb' h.1 h.2
  | _, .last _ u, .inr y, tb, tb', _, hcs => by
      rw [armHead.eq_3, armHead.eq_3]
      exact encHead_static_tb_irrel u y tb tb' (by simpa [isStaticC] using hcs)
  termination_by t cs => (sizeOf t + sizeOf cs, 0)
  decreasing_by all_goals simp_wf; all_goals first | omega | (have := Ctors.sizeOf_pos ‹Ctors›; omega)

end

/-! ### Side conditions -/

mutual

/-- Side conditions for the round trip: every array length fits in a word
    (without it, e.g. an `array unit` of length `2^256` encodes its length as `0`),
    and every enum on the value's path has pairwise-distinct constructor tags
    (without it, e.g. `enum "A" word (last "A" word)` decodes `inr 5` as `inl 5`).

    The tag condition is the round trip's assumption about `keccak256`. It is
    *local*: only the signature strings `"Name(argSigs)"` of the constructors of
    enums the value passes through must hash to distinct words, not keccak as a
    whole (which cannot be injective: it maps all byte strings to 256 bits, so a
    global injectivity axiom would be inconsistent). It holds when the
    signatures are distinct (solcore rejects duplicate constructor names, and
    distinct names give distinct signatures) and keccak has no collision among
    them, the standard cryptographic assumption. Since `keccak256` is opaque, it
    cannot be discharged by `decide`; for concrete types it is checked by native
    evaluation (the FFI), which trusts the C implementation. -/
def Fits : (t : Ty) → Value t → Prop
  | .unit, _ => True
  | .word, _ => True
  | .bool, _ => True
  | .pair a b, v => Fits a v.1 ∧ Fits b v.2
  | .sum a b, v => match v with
      | .inl x => Fits a x
      | .inr y => Fits b y
  | .tup a, v => Fits a v
  | .array a, xs => xs.length < 2 ^ 256 ∧ ∀ x ∈ xs, Fits a x
  | .enum n t cs, v => (ctorTag n t :: tagsC cs).Nodup ∧ match v with
      | .inl x => Fits t x
      | .inr y => FitsC cs y

/-- `Fits` for a value of one of the remaining constructors. -/
def FitsC : (cs : Ctors) → ValueC cs → Prop
  | .last _ u, y => Fits u y
  | .cons _ u _, v => match v with
      | .inl x => Fits u x
      | .inr y => FitsC _ y

end

/-- `Fits` for the selected payload of an enum. -/
def FitsArm (t : Ty) (cs : Ctors) : Value t ⊕ ValueC cs → Prop
  | .inl x => Fits t x
  | .inr y => FitsC cs y

theorem FitsArm_inl {t : Ty} {cs : Ctors} {x : Value t} (h : FitsArm t cs (Sum.inl x)) :
    Fits t x := by simpa only [FitsArm] using h

theorem FitsArm_cons_inr {t u : Ty} {m : String} {cs : Ctors} {y : ValueC (Ctors.cons m u cs)}
    (h : FitsArm t (Ctors.cons m u cs) (Sum.inr y)) : FitsArm u cs y := by
  cases y <;> simpa only [FitsArm, FitsC] using h

theorem FitsArm_last_inr {t u : Ty} {m : String} {y : ValueC (Ctors.last m u)}
    (h : FitsArm t (Ctors.last m u) (Sum.inr y)) : Fits u y := by
  simpa only [FitsArm, FitsC] using h

theorem Fits_enum {n : String} {t : Ty} {cs : Ctors} {v : Value (Ty.enum n t cs)}
    (h : Fits (Ty.enum n t cs) v) : (ctorTag n t :: tagsC cs).Nodup ∧ FitsArm t cs v := by
  cases v <;> exact h

/-! ### Reads -/

/-- A word read is the head of the corresponding suffix. -/
theorem rd_eq_drop (W : Wire) (k : Nat) : rd W k = (W.drop k).getD 0 0 := by
  simp [rd, List.getD_eq_getElem?_getD, List.getElem?_drop]

/-- A word sitting at the front of a suffix is what `rd` reads there. -/
theorem rd_of_drop {W : Wire} {k : Nat} {w : Word} {r : Wire}
    (h : W.drop k = w :: r) : rd W k = w := by
  rw [rd_eq_drop, h]; rfl

/-- Advancing a `drop` past a known head prefix. -/
theorem drop_add_length {α} (W : List α) (k : Nat) (l r : List α)
    (h : W.drop k = l ++ r) : W.drop (k + l.length) = r := by
  rw [← List.drop_drop, h, List.drop_left]

/-! ### The static fragment -/

mutual

/-- Placement lemma for the static fragment: if the head of `v` sits contiguously
    at `base + ho` in `W`, the base-relative decoder recovers `v`. Static types
    have no tail, so the head block is the whole encoding and reads never follow an
    offset. -/
theorem decAt_static : ∀ (t : Ty), isStatic t = true →
    ∀ (v : Value t) (W : Wire) (base ho : Nat) (suf : Wire), Fits t v →
      W.drop (base + ho) = encHead t v (headWords t) ++ suf → decAt t W base ho = v
  | .unit => by intro _ v W base ho suf _ _; simp only [decAt]
  | .word => by
      intro _ v W base ho suf _ hp
      simp only [decAt, rd_eq_drop, hp, encHead]; rfl
  | .bool => by
      intro _ v W base ho suf _ hp
      have hh : encHead Ty.bool v (headWords Ty.bool) = [bif v then (1 : Word) else 0] := by
        simp only [encHead]
      rw [hh] at hp
      have hv : rd W (base + ho) = (bif v then (1 : Word) else 0) := by
        rw [rd_eq_drop, hp]; rfl
      simp only [decAt, hv]
      cases v <;> rfl
  | .pair a b => by
      intro hst v W base ho suf hfit hp
      simp only [isStatic, Bool.and_eq_true] at hst
      obtain ⟨hsa, hsb⟩ := hst
      have hea : encTail a v.1 = [] := encTail_nil_of_static a v.1 hsa
      have hpair : encHead (Ty.pair a b) v (headWords (Ty.pair a b))
          = encHead a v.1 (headWords a) ++ encHead b v.2 (headWords b) := by
        simp only [encHead, hea, List.length_nil, Nat.add_zero]
        rw [encHead_static_tb_irrel a v.1 (headWords (Ty.pair a b)) (headWords a) hsa,
            encHead_static_tb_irrel b v.2 (headWords (Ty.pair a b)) (headWords b) hsb]
      rw [hpair, List.append_assoc] at hp
      have hla : (encHead a v.1 (headWords a)).length = headWords a := encHead_length a v.1 _
      have ha := decAt_static a hsa v.1 W base ho _ hfit.1 hp
      have hpb : W.drop (base + (ho + headWords a))
          = encHead b v.2 (headWords b) ++ suf := by
        have hd := drop_add_length W (base + ho) (encHead a v.1 (headWords a))
          (encHead b v.2 (headWords b) ++ suf) hp
        rwa [hla, show (base + ho) + headWords a = base + (ho + headWords a) from by omega] at hd
      have hb := decAt_static b hsb v.2 W base (ho + headWords a) suf hfit.2 hpb
      simp only [decAt]; rw [ha, hb]
  | .sum a b => by
      intro hst v W base ho suf hfit hp
      have hstb : (isStatic a && isStatic b) = true := by simpa only [isStatic] using hst
      simp only [isStatic, Bool.and_eq_true] at hst
      obtain ⟨hsa, hsb⟩ := hst
      cases v with
      | inl x =>
          have hhead : encHead (Ty.sum a b) (Sum.inl x) (headWords (Ty.sum a b))
              = (0 : Word) :: (encHead a x (headWords a) ++ List.replicate (padL a b) 0) := by
            simp only [encHead]
            rw [if_pos hstb, encHead_static_tb_irrel a x (headWords (Ty.sum a b)) (headWords a) hsa]
          rw [hhead] at hp
          have htag : rd W (base + ho) = 0 := by rw [rd_eq_drop, hp]; rfl
          have hpa : W.drop (base + (ho + 1))
              = encHead a x (headWords a) ++ (List.replicate (padL a b) 0 ++ suf) := by
            have hp' : W.drop (base + ho)
                = [(0 : Word)] ++ (encHead a x (headWords a)
                    ++ (List.replicate (padL a b) 0 ++ suf)) := by
              rw [hp]; simp [List.append_assoc]
            have hd := drop_add_length W (base + ho) [(0 : Word)]
              (encHead a x (headWords a) ++ (List.replicate (padL a b) 0 ++ suf)) hp'
            simpa [show (base + ho) + 1 = base + (ho + 1) from by omega] using hd
          have ha := decAt_static a hsa x W base (ho + 1) _ hfit hpa
          simp only [decAt]; simp [hstb, htag]; try rw [ha]
      | inr y =>
          have hhead : encHead (Ty.sum a b) (Sum.inr y) (headWords (Ty.sum a b))
              = (1 : Word) :: (encHead b y (headWords b) ++ List.replicate (padR a b) 0) := by
            simp only [encHead]
            rw [if_pos hstb, encHead_static_tb_irrel b y (headWords (Ty.sum a b)) (headWords b) hsb]
          rw [hhead] at hp
          have htag : rd W (base + ho) = 1 := by rw [rd_eq_drop, hp]; rfl
          have hpb : W.drop (base + (ho + 1))
              = encHead b y (headWords b) ++ (List.replicate (padR a b) 0 ++ suf) := by
            have hp' : W.drop (base + ho)
                = [(1 : Word)] ++ (encHead b y (headWords b)
                    ++ (List.replicate (padR a b) 0 ++ suf)) := by
              rw [hp]; simp [List.append_assoc]
            have hd := drop_add_length W (base + ho) [(1 : Word)]
              (encHead b y (headWords b) ++ (List.replicate (padR a b) 0 ++ suf)) hp'
            simpa [show (base + ho) + 1 = base + (ho + 1) from by omega] using hd
          have hb := decAt_static b hsb y W base (ho + 1) _ hfit hpb
          simp only [decAt]; simp [hstb, htag]; try rw [hb]
  | .tup a => by
      intro hst v W base ho suf hfit hp
      have hsa : isStatic a = true := by simpa only [isStatic] using hst
      have hhead : encHead (Ty.tup a) v (headWords (Ty.tup a)) = encHead a v (headWords a) := by
        simp only [encHead, headWords, hsa, if_pos]
      rw [hhead] at hp
      simp only [decAt]
      rw [decAt_static a hsa v W base ho suf hfit hp]
      exact if_pos hsa
  | .array a => by intro hst; simp only [isStatic] at hst; exact absurd hst (by decide)
  | .enum n t cs => by
      intro hst v W base ho suf hfit hp
      have hs : (isStatic t && isStaticC cs) = true := by simpa only [isStatic] using hst
      have hs' : isStatic t = true ∧ isStaticC cs = true := by simpa using hs
      have hf := Fits_enum hfit
      have hhead : encHead (Ty.enum n t cs) v (headWords (Ty.enum n t cs))
          = armTag n t cs v :: (armHead t cs v (headWords (Ty.enum n t cs))
              ++ List.replicate (max (headWords t) (headWordsC cs) - armWords t cs v) 0) := by
        simp only [encHead]; rw [if_pos hs]
      rw [hhead] at hp
      have htag : rd W (base + ho) = armTag n t cs v := rd_of_drop (by simpa using hp)
      have hpa : W.drop (base + (ho + 1))
          = armHead t cs v (headWords (Ty.enum n t cs))
            ++ (List.replicate (max (headWords t) (headWordsC cs) - armWords t cs v) 0 ++ suf) := by
        have hd := drop_add_length W (base + ho) [armTag n t cs v] _ (by simpa using hp)
        simpa [Nat.add_assoc] using hd
      simp only [decAt]; rw [if_pos hs, htag]
      exact decArm_static n t cs v W base (ho + 1) _ _ hs'.1 hs'.2 hf.1 hf.2 hpa
  termination_by t => (sizeOf t, 1)

/-- Static placement lemma for the selected payload of an enum: `decArm`, given
    the written tag, recovers the selected constructor and its payload. -/
theorem decArm_static : ∀ (n : String) (t : Ty) (cs : Ctors) (v : Value t ⊕ ValueC cs)
    (W : Wire) (base ho tb : Nat) (suf : Wire),
    isStatic t = true → isStaticC cs = true →
    (ctorTag n t :: tagsC cs).Nodup → FitsArm t cs v →
    W.drop (base + ho) = armHead t cs v tb ++ suf →
    decArm n t cs W base ho (armTag n t cs v) = v
  | n, t, .cons m u cs, .inl x => by
      intro W base ho tb suf hst _ _ hf hp
      rw [armHead.eq_1] at hp
      rw [encHead_static_tb_irrel t x tb (headWords t) hst] at hp
      have hx := decAt_static t hst x W base ho suf (FitsArm_inl hf) hp
      simp [armTag, decArm, hx]
  | n, t, .cons m u cs, .inr y => by
      intro W base ho tb suf _ hcs hnd hf hp
      have h : isStatic u = true ∧ isStaticC cs = true := by simpa [isStaticC] using hcs
      have hne := armTag_inr_ne (y := y) hnd
      have hnd' : (ctorTag m u :: tagsC cs).Nodup := by
        simpa [tagsC] using (List.nodup_cons.mp hnd).2
      rw [armHead.eq_2] at hp
      have hy := decArm_static m u cs y W base ho tb suf h.1 h.2 hnd' (FitsArm_cons_inr hf) hp
      simp only [armTag] at hne ⊢
      simp [decArm, hne, hy]
  | n, t, .last m u, .inl x => by
      intro W base ho tb suf hst _ _ hf hp
      rw [armHead.eq_1] at hp
      rw [encHead_static_tb_irrel t x tb (headWords t) hst] at hp
      have hx := decAt_static t hst x W base ho suf (FitsArm_inl hf) hp
      simp [armTag, decArm, hx]
  | n, t, .last m u, .inr y => by
      intro W base ho tb suf _ hcs hnd hf hp
      have hsu : isStatic u = true := by simpa [isStaticC] using hcs
      have hne := armTag_inr_ne (y := y) hnd
      rw [armHead.eq_3] at hp
      rw [encHead_static_tb_irrel u y tb (headWords u) hsu] at hp
      have hy := decAt_static u hsu y W base ho suf (FitsArm_last_inr hf) hp
      simp only [armTag] at hne ⊢
      simp [decArm, hne, hy]
  termination_by _ t cs => (sizeOf t + sizeOf cs, 0)
  decreasing_by all_goals simp_wf; all_goals first | omega | (have := Ctors.sizeOf_pos ‹Ctors›; omega)

end

/-- Retraction (T1) for the static fragment: decoding a canonical encoding
    recovers the value. Dynamic arrays are validated by the machine-checked
    round-trip battery in `AbiModel/Sanity.lean`. -/
theorem decode_encode_static (t : Ty) (hst : isStatic t = true) (v : Value t)
    (hfit : Fits t v) : decode t (encode t v) = v := by
  have hnil : encTail t v = [] := encTail_nil_of_static t v hst
  have hp : (encode t v).drop (0 + 0) = encHead t v (headWords t) ++ [] := by
    simp [encode, hnil]
  simpa [decode] using decAt_static t hst v (encode t v) 0 0 [] hfit hp

theorem decodeAll_encode_static (t : Ty) (hst : isStatic t = true) (v : Value t)
    (hfit : Fits t v) : decodeAll t (encode t v) = some v := by
  simp [decodeAll, decode_encode_static t hst v hfit]

/-! ### Base-relative decoding -/

/-- Reads are base-relative: prepending `pre` and shifting the base by its
    length does not change the read. -/
theorem rd_shift (pre W : Wire) (k : Nat) : rd (pre ++ W) (pre.length + k) = rd W k := by
  simp [rd, List.getD_eq_getElem?_getD, List.getElem?_append_right]

mutual

/-- The decoder is base-relative: prepending `pre` to the wire and shifting the
    base by its length decodes the same value. -/
theorem decAt_shift : ∀ (t : Ty) (pre W : Wire) (base ho : Nat),
    decAt t (pre ++ W) (pre.length + base) ho = decAt t W base ho
  | .unit => by intros; rfl
  | .word => by intro pre W base ho; simp only [decAt, Nat.add_assoc, rd_shift]
  | .bool => by intro pre W base ho; simp only [decAt, Nat.add_assoc, rd_shift]
  | .pair a b => by intro pre W base ho; simp only [decAt, decAt_shift a, decAt_shift b]
  | .sum a b => by
      intro pre W base ho
      simp only [decAt, Nat.add_assoc, rd_shift, decAt_shift a, decAt_shift b]
  | .tup a => by intro pre W base ho; simp only [decAt, Nat.add_assoc, rd_shift, decAt_shift a]
  | .array a => by
      have hseq : ∀ (pre W : Wire) (region n i : Nat),
          decSeq a (pre ++ W) (pre.length + region) n i = decSeq a W region n i := by
        intro pre W region n
        induction n with
        | zero => intro i; simp only [decSeq]
        | succ k ih => intro i; simp only [decSeq, decAt_shift a, ih]
      intro pre W base ho; simp only [decAt, Nat.add_assoc, rd_shift, hseq]
  | .enum n t cs => by
      intro pre W base ho
      simp only [decAt, Nat.add_assoc, rd_shift, decArm_shift n t cs]
  termination_by t => (sizeOf t, 1)

/-- `decArm` is base-relative. -/
theorem decArm_shift : ∀ (n : String) (t : Ty) (cs : Ctors) (pre W : Wire) (base ho : Nat)
    (tag : Word), decArm n t cs (pre ++ W) (pre.length + base) ho tag = decArm n t cs W base ho tag
  | _, t, .cons m u cs => by
      intro pre W base ho tag; simp only [decArm, decAt_shift t, decArm_shift m u cs]
  | _, t, .last _ u => by
      intro pre W base ho tag; simp only [decArm, decAt_shift t, decAt_shift u]
  termination_by _ t cs => (sizeOf t + sizeOf cs, 0)
  decreasing_by all_goals simp_wf; all_goals first | omega | (have := Ctors.sizeOf_pos ‹Ctors›; omega)

end

/-! ### The dynamic fragment -/

/-- A dynamic type has a nonempty head (at least its offset word). -/
theorem headWords_pos_of_dynamic : ∀ (t : Ty), isStatic t = false → 0 < headWords t
  | .unit => by intro h; simp [isStatic] at h
  | .word => by intro h; simp [isStatic] at h
  | .bool => by intro h; simp [isStatic] at h
  | .pair a b => by
      intro h
      simp only [isStatic, Bool.and_eq_false_iff] at h
      simp only [headWords]
      rcases h with h | h
      · have := headWords_pos_of_dynamic a h; omega
      · have := headWords_pos_of_dynamic b h; omega
  | .sum a b => by intro _; simp only [headWords]; split <;> omega
  | .tup a => by intro h; simp [isStatic] at h; simp [headWords, h]
  | .array a => by intro _; simp [headWords]
  | .enum n t cs => by intro _; simp only [headWords]; split <;> omega
  termination_by t => sizeOf t

/-- The element heads of an array occupy `length × headWords a` words. -/
theorem encHeadSeq_length (a : Ty) : ∀ (xs : List (Value a)) (tb : Nat),
    (encHeadSeq a xs tb).length = xs.length * headWords a := by
  intro xs
  induction xs with
  | nil => intro tb; simp [encHeadSeq]
  | cons x xs ih =>
      intro tb
      simp only [encHeadSeq, List.length_append, encHead_length, ih, List.length_cons,
        Nat.succ_mul]
      omega

/-- If the suffix at `k` starts with a nonempty block, `k` is in range. -/
theorem lt_length_of_drop {W : Wire} {k : Nat} {l r : Wire}
    (h : W.drop k = l ++ r) (hl : 0 < l.length) : k < W.length := by
  apply Classical.byContradiction
  intro hk
  rw [List.drop_eq_nil_of_le (by omega)] at h
  have := congrArg List.length h
  simp at this; omega

theorem natW_toNat {n : Nat} (h : n < 2 ^ 256) : (natW n).toNat = n := by
  simp [natW, Nat.mod_eq_of_lt h]

mutual

/-- General placement lemma: if the head of `v` (written with tail cursor `tb`)
    sits at `base + ho` and its tail sits at `base + tb`, the base-relative
    decoder recovers `v`. Offsets and lengths must fit in a word. -/
theorem decAt_place : ∀ (t : Ty) (v : Value t) (W : Wire) (base ho tb : Nat) (s1 s2 : Wire),
    Fits t v → W.length < 2 ^ 256 →
    W.drop (base + ho) = encHead t v tb ++ s1 →
    W.drop (base + tb) = encTail t v ++ s2 →
    decAt t W base ho = v
  | .unit => by intros; rfl
  | .word => by
      intro v W base ho tb s1 s2 _ _ hp _
      simp only [decAt]; exact rd_of_drop (by simpa [encHead] using hp)
  | .bool => by
      intro v W base ho tb s1 s2 _ _ hp _
      have hv : rd W (base + ho) = (bif v then (1 : Word) else 0) :=
        rd_of_drop (by simpa only [encHead, List.singleton_append] using hp)
      simp only [decAt, hv]
      cases v <;> rfl
  | .pair a b => by
      intro v W base ho tb s1 s2 hfit hlen hp ht
      simp only [encHead, List.append_assoc] at hp
      simp only [encTail, List.append_assoc] at ht
      have ha := decAt_place a v.1 W base ho tb _ _ hfit.1 hlen hp ht
      have hpb := drop_add_length W (base + ho) _ _ hp
      rw [encHead_length, Nat.add_assoc] at hpb
      have htb := drop_add_length W (base + tb) _ _ ht
      rw [Nat.add_assoc] at htb
      have hb := decAt_place b v.2 W base (ho + headWords a) _ _ _ hfit.2 hlen hpb htb
      simp only [decAt]; rw [ha, hb]
  | .sum a b => by
      intro v W base ho tb s1 s2 hfit hlen hp ht
      by_cases hs : (isStatic a && isStatic b) = true
      · have hst : isStatic (Ty.sum a b) = true := by simpa only [isStatic] using hs
        rw [encHead_static_tb_irrel _ v tb (headWords (Ty.sum a b)) hst] at hp
        exact decAt_static _ hst v W base ho s1 hfit hp
      · simp only [Bool.not_eq_true] at hs
        cases v with
        | inl x =>
            have hp' : W.drop (base + ho) = natW tb :: s1 := by simpa [encHead, hs] using hp
            have ht' : W.drop (base + tb)
                = ([(0 : Word)] ++ encHead a x (1 + max (headWords a) (headWords b))
                    ++ List.replicate (padL a b) 0) ++ (encTail a x ++ s2) := by
              simpa [encTail, hs] using ht
            have hlt : base + tb < W.length := lt_length_of_drop ht' (by simp)
            have hoff : (rd W (base + ho)).toNat = tb := by
              rw [rd_of_drop hp', natW_toNat (by omega)]
            have htag : rd W (base + tb) = 0 := rd_of_drop (by simpa using ht')
            have hpa : W.drop (base + tb + 1)
                = encHead a x (1 + max (headWords a) (headWords b))
                  ++ (List.replicate (padL a b) 0 ++ (encTail a x ++ s2)) := by
              have hd := drop_add_length W (base + tb) [(0 : Word)] _ (by simpa using ht')
              simpa using hd
            have hta : W.drop (base + tb + (1 + max (headWords a) (headWords b)))
                = encTail a x ++ s2 := by
              have hd := drop_add_length W (base + tb) _ _ ht'
              have hl : ([(0 : Word)] ++ encHead a x (1 + max (headWords a) (headWords b))
                  ++ List.replicate (padL a b) 0).length = 1 + max (headWords a) (headWords b) := by
                simp only [List.length_append, encHead_length, List.length_replicate, padL,
                  List.length_singleton]
                omega
              rwa [hl] at hd
            have hx := decAt_place a x W (base + tb) 1 _ _ _ hfit hlen hpa hta
            simp [decAt, hs, hoff, htag, hx]
        | inr y =>
            have hp' : W.drop (base + ho) = natW tb :: s1 := by simpa [encHead, hs] using hp
            have ht' : W.drop (base + tb)
                = ([(1 : Word)] ++ encHead b y (1 + max (headWords a) (headWords b))
                    ++ List.replicate (padR a b) 0) ++ (encTail b y ++ s2) := by
              simpa [encTail, hs] using ht
            have hlt : base + tb < W.length := lt_length_of_drop ht' (by simp)
            have hoff : (rd W (base + ho)).toNat = tb := by
              rw [rd_of_drop hp', natW_toNat (by omega)]
            have htag : rd W (base + tb) = 1 := rd_of_drop (by simpa using ht')
            have hpb : W.drop (base + tb + 1)
                = encHead b y (1 + max (headWords a) (headWords b))
                  ++ (List.replicate (padR a b) 0 ++ (encTail b y ++ s2)) := by
              have hd := drop_add_length W (base + tb) [(1 : Word)] _ (by simpa using ht')
              simpa using hd
            have htb : W.drop (base + tb + (1 + max (headWords a) (headWords b)))
                = encTail b y ++ s2 := by
              have hd := drop_add_length W (base + tb) _ _ ht'
              have hl : ([(1 : Word)] ++ encHead b y (1 + max (headWords a) (headWords b))
                  ++ List.replicate (padR a b) 0).length = 1 + max (headWords a) (headWords b) := by
                simp only [List.length_append, encHead_length, List.length_replicate, padR,
                  List.length_singleton]
                omega
              rwa [hl] at hd
            have hy := decAt_place b y W (base + tb) 1 _ _ _ hfit hlen hpb htb
            simp [decAt, hs, hoff, htag, hy]
  | .tup a => by
      intro v W base ho tb s1 s2 hfit hlen hp ht
      by_cases hsa : isStatic a = true
      · have hst : isStatic (Ty.tup a) = true := by simpa only [isStatic] using hsa
        rw [encHead_static_tb_irrel _ v tb (headWords (Ty.tup a)) hst] at hp
        exact decAt_static _ hst v W base ho s1 hfit hp
      · simp only [Bool.not_eq_true] at hsa
        have hp' : W.drop (base + ho) = natW tb :: s1 := by simpa [encHead, hsa] using hp
        have ht' : W.drop (base + tb) = encHead a v (headWords a) ++ (encTail a v ++ s2) := by
          simpa [encTail, hsa] using ht
        have hlt : base + tb < W.length :=
          lt_length_of_drop ht' (by rw [encHead_length]; exact headWords_pos_of_dynamic a hsa)
        have hoff : (rd W (base + ho)).toNat = tb := by
          rw [rd_of_drop hp', natW_toNat (by omega)]
        have hta : W.drop (base + tb + headWords a) = encTail a v ++ s2 := by
          have hd := drop_add_length W _ _ _ ht'
          rwa [encHead_length] at hd
        have hx := decAt_place a v W (base + tb) 0 (headWords a) _ _ hfit hlen
          (by simpa using ht') hta
        simp [decAt, hsa, hoff, hx]
  | .array a => by
      intro v W base ho tb s1 s2 hfit hlen hp ht
      have hseq : ∀ (xs : List (Value a)) (region i tb' : Nat) (s1' s2' : Wire),
          (∀ x ∈ xs, Fits a x) →
          W.drop (region + i * headWords a) = encHeadSeq a xs tb' ++ s1' →
          W.drop (region + tb') = encTailSeq a xs ++ s2' →
          decSeq a W region xs.length i = xs := by
        intro xs
        induction xs with
        | nil => intros; simp [decSeq]
        | cons x xs ih =>
            intro region i tb' s1' s2' hf hph hpt
            simp only [encHeadSeq, List.append_assoc] at hph
            simp only [encTailSeq, List.append_assoc] at hpt
            have hx := decAt_place a x W region (i * headWords a) tb' _ _ (hf x (by simp)) hlen
              hph hpt
            have hph2 := drop_add_length W _ _ _ hph
            rw [encHead_length, Nat.add_assoc, ← Nat.succ_mul] at hph2
            have hpt2 := drop_add_length W _ _ _ hpt
            rw [Nat.add_assoc] at hpt2
            have hrest := ih region (i + 1) _ _ _ (fun y hy => hf y (by simp [hy])) hph2 hpt2
            simp only [List.length_cons, decSeq, hx, hrest]
      have hp' : W.drop (base + ho) = natW tb :: s1 := by simpa [encHead] using hp
      have ht' : W.drop (base + tb) = [natW v.length]
          ++ (encHeadSeq a v (v.length * headWords a) ++ (encTailSeq a v ++ s2)) := by
        simpa [encTail] using ht
      have hlt : base + tb < W.length := lt_length_of_drop ht' (by simp)
      have hoff : (rd W (base + ho)).toNat = tb := by
        rw [rd_of_drop hp', natW_toNat (by omega)]
      have hlenw : (rd W (base + tb)).toNat = v.length := by
        rw [rd_of_drop (by simpa using ht'), natW_toNat hfit.1]
      have hh := drop_add_length W _ _ _ ht'
      have ht2 := drop_add_length W _ _ _ hh
      rw [encHeadSeq_length, List.length_singleton] at ht2
      have hx := hseq v (base + tb + 1) 0 _ _ _ hfit.2 (by simpa using hh) ht2
      simp [decAt, hoff, hlenw, hx]
  | .enum n t cs => by
      intro v W base ho tb s1 s2 hfit hlen hp ht
      have hf := Fits_enum hfit
      by_cases hs : (isStatic t && isStaticC cs) = true
      · have hst : isStatic (Ty.enum n t cs) = true := by simpa only [isStatic] using hs
        rw [encHead_static_tb_irrel _ v tb (headWords (Ty.enum n t cs)) hst] at hp
        exact decAt_static _ hst v W base ho s1 hfit hp
      · simp only [Bool.not_eq_true] at hs
        have hp' : W.drop (base + ho) = natW tb :: s1 := by simpa [encHead, hs] using hp
        have ht' : W.drop (base + tb)
            = ([armTag n t cs v] ++ armHead t cs v (1 + max (headWords t) (maxArmC cs))
                ++ List.replicate (max (headWords t) (maxArmC cs) - armWords t cs v) 0)
              ++ (armTail t cs v ++ s2) := by
          simpa [encTail, hs] using ht
        have hlt : base + tb < W.length := lt_length_of_drop ht' (by simp)
        have hoff : (rd W (base + ho)).toNat = tb := by
          rw [rd_of_drop hp', natW_toNat (by omega)]
        have htag : rd W (base + tb) = armTag n t cs v := rd_of_drop (by simpa using ht')
        have hpa : W.drop (base + tb + 1)
            = armHead t cs v (1 + max (headWords t) (maxArmC cs))
              ++ (List.replicate (max (headWords t) (maxArmC cs) - armWords t cs v) 0
                ++ (armTail t cs v ++ s2)) := by
          have hd := drop_add_length W (base + tb) [armTag n t cs v] _ (by simpa using ht')
          simpa using hd
        have hta : W.drop (base + tb + (1 + max (headWords t) (maxArmC cs)))
            = armTail t cs v ++ s2 := by
          have hd := drop_add_length W (base + tb) _ _ ht'
          have hl : ([armTag n t cs v] ++ armHead t cs v (1 + max (headWords t) (maxArmC cs))
              ++ List.replicate (max (headWords t) (maxArmC cs) - armWords t cs v) 0).length
              = 1 + max (headWords t) (maxArmC cs) := by
            have := armWords_le_maxArm t cs v
            simp only [List.length_append, armHead_length, List.length_replicate,
              List.length_singleton]
            omega
          rwa [hl] at hd
        have hx := decArm_place n t cs v W (base + tb) 1 _ _ _ hf.1 hf.2 hlen hpa hta
        simp [decAt, hs, hoff, htag, hx]
  termination_by t => (sizeOf t, 1)

/-- Placement lemma for the selected payload of an enum: `decArm`, given the
    written tag, recovers the selected constructor and its payload. -/
theorem decArm_place : ∀ (n : String) (t : Ty) (cs : Ctors) (v : Value t ⊕ ValueC cs)
    (W : Wire) (base ho tb : Nat) (s1 s2 : Wire),
    (ctorTag n t :: tagsC cs).Nodup → FitsArm t cs v → W.length < 2 ^ 256 →
    W.drop (base + ho) = armHead t cs v tb ++ s1 →
    W.drop (base + tb) = armTail t cs v ++ s2 →
    decArm n t cs W base ho (armTag n t cs v) = v
  | n, t, .cons m u cs, .inl x => by
      intro W base ho tb s1 s2 _ hf hlen hp ht
      rw [armHead.eq_1] at hp
      rw [armTail.eq_1] at ht
      have hx := decAt_place t x W base ho tb s1 s2 (FitsArm_inl hf) hlen hp ht
      simp [armTag, decArm, hx]
  | n, t, .cons m u cs, .inr y => by
      intro W base ho tb s1 s2 hnd hf hlen hp ht
      have hne := armTag_inr_ne (y := y) hnd
      have hnd' : (ctorTag m u :: tagsC cs).Nodup := by
        simpa [tagsC] using (List.nodup_cons.mp hnd).2
      rw [armHead.eq_2] at hp
      rw [armTail.eq_2] at ht
      have hy := decArm_place m u cs y W base ho tb s1 s2 hnd' (FitsArm_cons_inr hf) hlen hp ht
      simp only [armTag] at hne ⊢
      simp [decArm, hne, hy]
  | n, t, .last m u, .inl x => by
      intro W base ho tb s1 s2 _ hf hlen hp ht
      rw [armHead.eq_1] at hp
      rw [armTail.eq_1] at ht
      have hx := decAt_place t x W base ho tb s1 s2 (FitsArm_inl hf) hlen hp ht
      simp [armTag, decArm, hx]
  | n, t, .last m u, .inr y => by
      intro W base ho tb s1 s2 hnd hf hlen hp ht
      have hne := armTag_inr_ne (y := y) hnd
      rw [armHead.eq_3] at hp
      rw [armTail.eq_3] at ht
      have hy := decAt_place u y W base ho tb s1 s2 (FitsArm_last_inr hf) hlen hp ht
      simp only [armTag] at hne ⊢
      simp [decArm, hne, hy]
  termination_by _ t cs => (sizeOf t + sizeOf cs, 0)
  decreasing_by all_goals simp_wf; all_goals first | omega | (have := Ctors.sizeOf_pos ‹Ctors›; omega)

end

/-- Retraction under the side conditions: `Fits t v` (array lengths fit in a
    word, enum constructor tags are distinct) and the whole encoding fits in a word.

    The length bound `hlen` is what makes offsets faithful: a dynamic node writes
    its tail position `tb` as `natW tb` (i.e. `tb mod 2^256`) and the decoder reads
    it back with `.toNat`, which recovers `tb` only if `tb < 2^256` (`natW_toNat`).
    Every tail position lies inside the wire, so `hlen` bounds all offsets at once.
    Without it, e.g. `pair (array word) (array word)` with more than `2^256`
    elements in the first array writes the second array's offset modulo `2^256`,
    and the decoder reads that array from the wrong place. No real calldata or
    memory comes near this size, so the bound excludes no encoding the EVM can
    hold. (It could be weakened to "every written offset is below `2^256`".) -/
theorem decode_encode_fits (t : Ty) (v : Value t) (hfit : Fits t v)
    (hlen : (encode t v).length < 2 ^ 256) : decode t (encode t v) = v := by
  have h1 : (encode t v).drop (0 + 0) = encHead t v (headWords t) ++ encTail t v := by
    simp [encode]
  have h2 := drop_add_length _ _ _ _ h1
  rw [encHead_length] at h2
  exact decAt_place t v (encode t v) 0 0 (headWords t) _ [] hfit hlen h1 (by simpa using h2)

/-- Retraction for dynamic types. Like `decode_encode_fits`, it needs the length
    bound so that offset words are not truncated modulo `2^256`; the static
    theorem `decode_encode_static` writes no offsets and needs no such bound. -/
theorem decode_encode_dynamic : ∀ (t : Ty), isStatic t = false → ∀ (v : Value t),
    Fits t v → (encode t v).length < 2 ^ 256 → decode t (encode t v) = v
  | .unit => by intro hdyn; exact absurd hdyn (by decide)
  | .word => by intro hdyn; exact absurd hdyn (by decide)
  | .bool => by intro hdyn; exact absurd hdyn (by decide)
  | .pair _ _ => fun _ v hfit hlen => decode_encode_fits _ v hfit hlen
  | .sum _ _ => fun _ v hfit hlen => decode_encode_fits _ v hfit hlen
  | .tup a => by
      intro hdyn v hfit hlen
      have hdyna : isStatic a = false := by simpa only [isStatic] using hdyn
      -- a dynamic tuple is one offset word (pointing just past itself) followed
      -- by the encoding of its contents
      have hW : encode (Ty.tup a) v = [natW 1] ++ encode a v := by
        simp [encode, encHead, encTail, headWords, hdyna]
      have h0 : (rd (encode (Ty.tup a) v) 0).toNat = 1 := by
        rw [hW]; simp [rd, natW]
      show decAt (Ty.tup a) (encode (Ty.tup a) v) 0 0 = v
      simp only [decAt, hdyna, Bool.false_eq_true, if_false, Nat.zero_add, h0]
      rw [hW]
      have hs := decAt_shift a [natW 1] (encode a v) 0 0
      simp only [List.length_singleton, Nat.add_zero] at hs
      rw [hs]
      exact decode_encode_dynamic a hdyna v hfit (by rw [hW] at hlen; simp at hlen; omega)
  | .array _ => fun _ v hfit hlen => decode_encode_fits _ v hfit hlen
  | .enum _ _ _ => fun _ v hfit hlen => decode_encode_fits _ v hfit hlen
  termination_by t => sizeOf t

end AbiModel
