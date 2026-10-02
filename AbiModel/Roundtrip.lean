import AbiModel.Decode

namespace AbiModel

/-- The head of any value has exactly `headWords t` words. -/
theorem encHead_length : ∀ (t : Ty) (v : Value t) (tb : Nat),
    (encHead t v tb).length = headWords t := by
  intro t
  induction t with
  | unit => intro v tb; simp only [encHead, headWords]; rfl
  | word => intro v tb; simp only [encHead, headWords]; rfl
  | bool => intro v tb; simp only [encHead, headWords]; rfl
  | pair a b iha ihb => intro v tb; simp only [encHead, headWords, List.length_append, iha, ihb]
  | sum a b iha ihb =>
      intro v tb
      by_cases hs : (isStatic a && isStatic b) = true
      · cases v with
        | inl x => simp [encHead, headWords, hs, iha, padL]; omega
        | inr y => simp [encHead, headWords, hs, ihb, padR]; omega
      · simp only [Bool.not_eq_true] at hs
        cases v with
        | inl x => simp [encHead, headWords, hs]
        | inr y => simp [encHead, headWords, hs]
  | tup a iha =>
      intro v tb
      by_cases hs : isStatic a = true
      · simp only [encHead, headWords, hs, if_pos]; exact iha v tb
      · simp only [Bool.not_eq_true] at hs
        simp only [encHead, headWords]; simp [hs]
  | array a _ => intro v tb; simp only [encHead, headWords]; rfl

/-- A static type has no tail. -/
theorem encTail_nil_of_static : ∀ (t : Ty) (v : Value t),
    isStatic t = true → encTail t v = [] := by
  intro t
  induction t with
  | unit => intro v _; simp only [encTail]
  | word => intro v _; simp only [encTail]
  | bool => intro v _; simp only [encTail]
  | pair a b iha ihb =>
      intro v h
      simp only [isStatic, Bool.and_eq_true] at h
      simp only [encTail, iha v.1 h.1, ihb v.2 h.2, List.append_nil]
  | sum a b _ _ =>
      intro v h
      simp only [isStatic] at h
      cases v <;> simp [encTail, h]
  | tup a _ =>
      intro v h
      simp only [isStatic] at h
      simp [encTail, h]
  | array a _ => intro v h; simp [isStatic] at h

/-- For a static type the head does not depend on the tail cursor. -/
theorem encHead_static_tb_irrel : ∀ (t : Ty) (v : Value t) (tb tb' : Nat),
    isStatic t = true → encHead t v tb = encHead t v tb' := by
  intro t
  induction t with
  | unit => intro v tb tb' _; simp [encHead]
  | word => intro v tb tb' _; simp [encHead]
  | bool => intro v tb tb' _; simp [encHead]
  | pair a b iha ihb =>
      intro v tb tb' h
      simp only [isStatic, Bool.and_eq_true] at h
      have hta : encTail a v.1 = [] := encTail_nil_of_static a v.1 h.1
      simp only [encHead, hta, List.length_nil, Nat.add_zero]
      rw [iha v.1 tb tb' h.1, ihb v.2 tb tb' h.2]
  | sum a b iha ihb =>
      intro v tb tb' h
      have hs : (isStatic a && isStatic b) = true := by simp only [isStatic] at h; exact h
      simp only [isStatic, Bool.and_eq_true] at h
      cases v with
      | inl x => simp only [encHead, hs, if_true]; rw [iha x tb tb' h.1]
      | inr y => simp only [encHead, hs, if_true]; rw [ihb y tb tb' h.2]
  | tup a iha =>
      intro v tb tb' h
      have hs : isStatic a = true := by simp only [isStatic] at h; exact h
      simp only [encHead, hs, if_true]
      exact iha v tb tb' hs
  | array a _ => intro v tb tb' h; simp [isStatic] at h

/-- A word read is the head of the corresponding suffix. -/
theorem rd_eq_drop (W : Wire) (k : Nat) : rd W k = (W.drop k).getD 0 0 := by
  simp [rd, List.getD_eq_getElem?_getD, List.getElem?_drop]

/-- Advancing a `drop` past a known head prefix. -/
theorem drop_add_length {α} (W : List α) (k : Nat) (l r : List α)
    (h : W.drop k = l ++ r) : W.drop (k + l.length) = r := by
  rw [← List.drop_drop, h, List.drop_left]

/-- Placement lemma for the static fragment: if the head of `v` sits contiguously
    at `base + ho` in `W`, the base-relative decoder recovers `v`. Static types
    have no tail, so the head block is the whole encoding and reads never follow an
    offset. -/
theorem decAt_static : ∀ (t : Ty), isStatic t = true →
    ∀ (v : Value t) (W : Wire) (base ho : Nat) (suf : Wire),
      W.drop (base + ho) = encHead t v (headWords t) ++ suf → decAt t W base ho = v := by
  intro t
  induction t with
  | unit => intro _ v W base ho suf _; simp only [decAt]; cases v; rfl
  | word =>
      intro _ v W base ho suf hp
      simp only [decAt, rd_eq_drop, hp, encHead]; rfl
  | bool =>
      intro _ v W base ho suf hp
      have hh : encHead Ty.bool v (headWords Ty.bool) = [bif v then (1 : Word) else 0] := by
        simp only [encHead]
      rw [hh] at hp
      have hv : rd W (base + ho) = (bif v then (1 : Word) else 0) := by
        rw [rd_eq_drop, hp]; rfl
      simp only [decAt, hv]
      cases v <;> rfl
  | pair a b iha ihb =>
      intro hst v W base ho suf hp
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
      have ha := iha hsa v.1 W base ho _ hp
      have hpb : W.drop (base + (ho + headWords a))
          = encHead b v.2 (headWords b) ++ suf := by
        have hd := drop_add_length W (base + ho) (encHead a v.1 (headWords a))
          (encHead b v.2 (headWords b) ++ suf) hp
        rwa [hla, show (base + ho) + headWords a = base + (ho + headWords a) from by omega] at hd
      have hb := ihb hsb v.2 W base (ho + headWords a) suf hpb
      simp only [decAt]; rw [ha, hb]
      rfl
  | sum a b iha ihb =>
      intro hst v W base ho suf hp
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
          have ha := iha hsa x W base (ho + 1) _ hpa
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
          have hb := ihb hsb y W base (ho + 1) _ hpb
          simp only [decAt]; simp [hstb, htag]; try rw [hb]
  | tup a iha =>
      intro hst v W base ho suf hp
      have hsa : isStatic a = true := by simpa only [isStatic] using hst
      have hhead : encHead (Ty.tup a) v (headWords (Ty.tup a)) = encHead a v (headWords a) := by
        simp only [encHead, headWords, hsa, if_pos]
      rw [hhead] at hp
      simp only [decAt]
      rw [iha hsa v W base ho suf hp]
      exact if_pos hsa
  | array a _ => intro hst; simp only [isStatic] at hst; exact absurd hst (by decide)

/-- Retraction (T1) for the static fragment: decoding a canonical encoding
    recovers the value. Dynamic arrays are validated by the machine-checked
    round-trip battery in `AbiModel/Sanity.lean`. -/
theorem decode_encode_static (t : Ty) (hst : isStatic t = true) (v : Value t) :
    decode t (encode t v) = v := by
  have hnil : encTail t v = [] := encTail_nil_of_static t v hst
  have hp : (encode t v).drop (0 + 0) = encHead t v (headWords t) ++ [] := by
    simp [encode, hnil]
  simpa [decode] using decAt_static t hst v (encode t v) 0 0 [] hp

theorem decodeAll_encode_static (t : Ty) (hst : isStatic t = true) (v : Value t) :
    decodeAll t (encode t v) = some v := by
  simp [decodeAll, decode_encode_static t hst v]

theorem decode_encode_dynamic (t : Ty) (hdyn : isStatic t = false) (v : Value t) :
  decode t (encode t v) = v := by
  induction t with
  | unit => exact absurd hdyn (by decide)
  | word => exact absurd hdyn (by decide)
  | bool => exact absurd hdyn (by decide)
  | pair a b ia ib =>
      -- proof for pair goes here
      sorry
  | sum a b ia ib =>
      -- proof for sum goes here
      sorry
  | tup a ia =>
      have hdyna : isStatic a = false := by simpa only [isStatic] using hdyn
      simp only [decode, decAt]
      rw [hdyna]
      simp [Value] at v
      simp
      have hfoo := ia hdyna v
      sorry
      -- proof for tuple goes here
  | array a ia =>
      -- proof for array goes here
      sorry

end AbiModel
