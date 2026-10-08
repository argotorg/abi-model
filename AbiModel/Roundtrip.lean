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
  | unit => intro _ v W base ho suf _; simp only [decAt]
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

/-- Reads are base-relative: prepending `pre` and shifting the base by its
    length does not change the read. -/
theorem rd_shift (pre W : Wire) (k : Nat) : rd (pre ++ W) (pre.length + k) = rd W k := by
  simp [rd, List.getD_eq_getElem?_getD, List.getElem?_append_right]

/-- The decoder is base-relative: prepending `pre` to the wire and shifting the
    base by its length decodes the same value. -/
theorem decAt_shift : ∀ (t : Ty) (pre W : Wire) (base ho : Nat),
    decAt t (pre ++ W) (pre.length + base) ho = decAt t W base ho := by
  intro t
  induction t with
  | unit => intros; rfl
  | word => intro pre W base ho; simp only [decAt, Nat.add_assoc, rd_shift]
  | bool => intro pre W base ho; simp only [decAt, Nat.add_assoc, rd_shift]
  | pair a b iha ihb => intro pre W base ho; simp only [decAt, iha, ihb]
  | sum a b iha ihb => intro pre W base ho; simp only [decAt, Nat.add_assoc, rd_shift, iha, ihb]
  | tup a iha => intro pre W base ho; simp only [decAt, Nat.add_assoc, rd_shift, iha]
  | array a iha =>
      have hseq : ∀ (pre W : Wire) (region n i : Nat),
          decSeq a (pre ++ W) (pre.length + region) n i = decSeq a W region n i := by
        intro pre W region n
        induction n with
        | zero => intro i; simp only [decSeq]
        | succ k ih => intro i; simp only [decSeq, iha, ih]
      intro pre W base ho; simp only [decAt, Nat.add_assoc, rd_shift, hseq]

/-- Size side-condition for the round trip: every array length fits in a word.
    (Without it, e.g. an `array unit` of length `2^256` encodes its length as `0`.) -/
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

/-- A dynamic type has a nonempty head (at least its offset word). -/
theorem headWords_pos_of_dynamic : ∀ (t : Ty), isStatic t = false → 0 < headWords t := by
  intro t
  induction t with
  | unit => intro h; simp [isStatic] at h
  | word => intro h; simp [isStatic] at h
  | bool => intro h; simp [isStatic] at h
  | pair a b iha ihb =>
      intro h
      simp only [isStatic, Bool.and_eq_false_iff] at h
      simp only [headWords]
      rcases h with h | h
      · have := iha h; omega
      · have := ihb h; omega
  | sum a b _ _ => intro _; simp only [headWords]; split <;> omega
  | tup a _ => intro h; simp [isStatic] at h; simp [headWords, h]
  | array a _ => intro _; simp [headWords]

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

/-- A word sitting at the front of a suffix is what `rd` reads there. -/
theorem rd_of_drop {W : Wire} {k : Nat} {w : Word} {r : Wire}
    (h : W.drop k = w :: r) : rd W k = w := by
  rw [rd_eq_drop, h]; rfl

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

/-- General placement lemma: if the head of `v` (written with tail cursor `tb`)
    sits at `base + ho` and its tail sits at `base + tb`, the base-relative
    decoder recovers `v`. Offsets and lengths must fit in a word. -/
theorem decAt_place : ∀ (t : Ty) (v : Value t) (W : Wire) (base ho tb : Nat) (s1 s2 : Wire),
    Fits t v → W.length < 2 ^ 256 →
    W.drop (base + ho) = encHead t v tb ++ s1 →
    W.drop (base + tb) = encTail t v ++ s2 →
    decAt t W base ho = v := by
  intro t
  induction t with
  | unit => intros; rfl
  | word =>
      intro v W base ho tb s1 s2 _ _ hp _
      simp only [decAt]; exact rd_of_drop (by simpa [encHead] using hp)
  | bool =>
      intro v W base ho tb s1 s2 _ _ hp _
      have hv : rd W (base + ho) = (bif v then (1 : Word) else 0) :=
        rd_of_drop (by simpa only [encHead, List.singleton_append] using hp)
      simp only [decAt, hv]
      cases v <;> rfl
  | pair a b iha ihb =>
      intro v W base ho tb s1 s2 hfit hlen hp ht
      simp only [encHead, List.append_assoc] at hp
      simp only [encTail, List.append_assoc] at ht
      have ha := iha v.1 W base ho tb _ _ hfit.1 hlen hp ht
      have hpb := drop_add_length W (base + ho) _ _ hp
      rw [encHead_length, Nat.add_assoc] at hpb
      have htb := drop_add_length W (base + tb) _ _ ht
      rw [Nat.add_assoc] at htb
      have hb := ihb v.2 W base (ho + headWords a) _ _ _ hfit.2 hlen hpb htb
      simp only [decAt]; rw [ha, hb]
  | sum a b iha ihb =>
      intro v W base ho tb s1 s2 hfit hlen hp ht
      by_cases hs : (isStatic a && isStatic b) = true
      · have hst : isStatic (Ty.sum a b) = true := by simpa only [isStatic] using hs
        rw [encHead_static_tb_irrel _ v tb (headWords (Ty.sum a b)) hst] at hp
        exact decAt_static _ hst v W base ho s1 hp
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
            have hx := iha x W (base + tb) 1 _ _ _ hfit hlen hpa hta
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
            have hy := ihb y W (base + tb) 1 _ _ _ hfit hlen hpb htb
            simp [decAt, hs, hoff, htag, hy]
  | tup a iha =>
      intro v W base ho tb s1 s2 hfit hlen hp ht
      by_cases hsa : isStatic a = true
      · have hst : isStatic (Ty.tup a) = true := by simpa only [isStatic] using hsa
        rw [encHead_static_tb_irrel _ v tb (headWords (Ty.tup a)) hst] at hp
        exact decAt_static _ hst v W base ho s1 hp
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
        have hx := iha v W (base + tb) 0 (headWords a) _ _ hfit hlen (by simpa using ht') hta
        simp [decAt, hsa, hoff, hx]
  | array a iha =>
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
            have hx := iha x W region (i * headWords a) tb' _ _ (hf x (by simp)) hlen hph hpt
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

/-- Retraction under the size side-conditions: every array length and the whole
    encoding fit in a word. -/
theorem decode_encode_fits (t : Ty) (v : Value t) (hfit : Fits t v)
    (hlen : (encode t v).length < 2 ^ 256) : decode t (encode t v) = v := by
  have h1 : (encode t v).drop (0 + 0) = encHead t v (headWords t) ++ encTail t v := by
    simp [encode]
  have h2 := drop_add_length _ _ _ _ h1
  rw [encHead_length] at h2
  exact decAt_place t v (encode t v) 0 0 (headWords t) _ [] hfit hlen h1 (by simpa using h2)

theorem decode_encode_dynamic (t : Ty) (hdyn : isStatic t = false) (v : Value t)
    (hfit : Fits t v) (hlen : (encode t v).length < 2 ^ 256) :
  decode t (encode t v) = v := by
  induction t with
  | unit => exact absurd hdyn (by decide)
  | word => exact absurd hdyn (by decide)
  | bool => exact absurd hdyn (by decide)
  | pair a b ia ib =>
      exact decode_encode_fits _ v hfit hlen
  | sum a b ia ib => exact decode_encode_fits _ v hfit hlen
  | tup a ia =>
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
      exact ia hdyna v hfit (by rw [hW] at hlen; simp at hlen; omega)
  | array a ia =>
      exact decode_encode_fits _ v hfit hlen

end AbiModel
