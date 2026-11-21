import AbiModel.Roundtrip
import AbiModel.DecodeStrict

/-!
# The strict decoder accepts the canonical encoding

`decStrict_encodeBytes`: on the byte-level encoding of `v` (`encodeBytes`, the
calldata arguments a caller sends), the strict decoder succeeds with `v`. Its
checks never fire on canonical input: every read is in bounds, every bool word
is `0` or `1`, every enum tag is a constructor's, and every array length passes
the std's overflow checks.

The proof mirrors `decAt_place`, at the byte level: the heads and tails are the
byte-scale `annHead 32` / `annTail 32` (offsets in bytes), and positions are
`32 ×` word indices.
-/

namespace AbiModel

/-! ### Byte-scale heads and tails -/

/-- The byte-scale head of `v` with tail cursor `tb`. -/
abbrev hB (t : Ty) (v : Value t) (tb : Nat) : Wire := (annHead 32 t v tb).map (·.val)
/-- The byte-scale tail of `v`. -/
abbrev tB (t : Ty) (v : Value t) : Wire := (annTail 32 t v).map (·.val)

theorem hB_length (t : Ty) (v : Value t) (tb : Nat) : (hB t v tb).length = headWords t := by
  rw [List.length_map, annHead_scale, List.length_map, ← List.length_map (f := (·.val)),
    annHead_one, encHead_length]

theorem tB_length (t : Ty) (v : Value t) : (tB t v).length = (encTail t v).length := by
  rw [List.length_map, annTail_scale, List.length_map, ← List.length_map (f := (·.val)),
    annTail_one]

theorem annArmHead32_length (t : Ty) (cs : Ctors) (v : Value t ⊕ ValueC cs) (tb : Nat) :
    (annArmHead 32 t cs v tb).length = armWords t cs v := by
  rw [annArmHead_scale, List.length_map, ← List.length_map (f := (·.val)),
    annArmHead_one, armHead_length]

theorem annHeadSeq32_length (a : Ty) (xs : List (Value a)) (tb : Nat) :
    (annHeadSeq 32 a xs tb).length = xs.length * elemWords a := by
  rw [annHeadSeq_scale, List.length_map, ← List.length_map (f := (·.val)),
    annHeadSeq_one, encHeadSeq_length]

theorem tB_nil_of_static (t : Ty) (v : Value t) (h : isStatic t = true) : tB t v = [] := by
  apply List.eq_nil_of_length_eq_zero
  rw [tB_length, encTail_nil_of_static t v h]; rfl

/-! ### The reader on a word-aligned input -/

/-- An input whose byte length is its words' (`Input.ofWire`). -/
def Input.Full (I : Input) : Prop := I.size = 32 * I.words.length

theorem wordAt_aligned (I : Input) (k : Nat) : I.wordAt (32 * k) = rd I.words k := by
  simp [Input.wordAt, Nat.mul_mod_right, Nat.mul_div_cancel_left k (by decide : 0 < 32)]

theorem read_ok {I : Input} (hI : I.Full) {k : Nat} (hk : k < I.words.length) :
    I.read (32 * k) = .ok (rd I.words k) := by
  have : 32 * k + 32 ≤ I.size := by rw [hI]; omega
  simp [Input.read, this, wordAt_aligned]; rfl

theorem adv_ok {I : Input} (hI : I.Full) {a b : Nat} (h : a + b ≤ I.words.length) :
    I.adv (32 * a) (32 * b) = .ok (32 * (a + b)) := by
  have : 32 * a + 32 * b ≤ I.size := by rw [hI]; omega
  simp [Input.adv, this, Nat.mul_add]; rfl

theorem readAt_ok {I : Input} (hI : I.Full) {a b : Nat} (h : a + b < I.words.length) :
    I.readAt (32 * a) (32 * b) = .ok (rd I.words (a + b)) := by
  simp only [Input.readAt, adv_ok hI (Nat.le_of_lt h), bind, Except.bind]
  exact read_ok hI h

theorem adv_ok_one {I : Input} (hI : I.Full) {a : Nat} (h : a + 1 ≤ I.words.length) :
    I.adv (32 * a) 32 = .ok (32 * (a + 1)) := adv_ok (b := 1) hI h

theorem armTail_nil_of_static : ∀ (t : Ty) (cs : Ctors) (v : Value t ⊕ ValueC cs),
    isStatic t = true → isStaticC cs = true → armTail t cs v = []
  | t, _, .inl x, ht, _ => by rw [armTail.eq_1]; exact encTail_nil_of_static t x ht
  | _, .cons _ u cs, .inr y, _, hc => by
      simp only [isStaticC, Bool.and_eq_true] at hc
      rw [armTail.eq_2]; exact armTail_nil_of_static u cs y hc.1 hc.2
  | _, .last _ u, .inr y, _, hc => by
      simp only [isStaticC] at hc
      rw [armTail.eq_3]; exact encTail_nil_of_static u y hc

theorem aTB_nil_of_static (t : Ty) (cs : Ctors) (v : Value t ⊕ ValueC cs)
    (ht : isStatic t = true) (hc : isStaticC cs = true) :
    (annArmTail 32 t cs v).map (·.val) = [] := by
  apply List.eq_nil_of_length_eq_zero
  rw [List.length_map, annArmTail_scale, List.length_map, ← List.length_map (f := (·.val)),
    annArmTail_one, armTail_nil_of_static t cs v ht hc]; rfl

theorem aHB_length (t : Ty) (cs : Ctors) (v : Value t ⊕ ValueC cs) (tb : Nat) :
    ((annArmHead 32 t cs v tb).map (·.val)).length = armWords t cs v := by
  rw [List.length_map, annArmHead32_length]

/-- `k + l.length ≤ W.length` when `l` follows position `k ≤ W.length`. -/
theorem le_length_of_drop {α} {W : List α} {k : Nat} {l r : List α}
    (h : W.drop k = l ++ r) (hk : k ≤ W.length) : k + l.length ≤ W.length := by
  have := congrArg List.length h
  simp only [List.length_drop, List.length_append] at this
  omega

/-! ### Placement -/

theorem ok_bind {α β} (x : α) (f : α → Dec β) : (Except.ok x >>= f) = f x := rfl

/-- The byte-scale head of an array element. -/
abbrev eHB (a : Ty) (x : Value a) (tb : Nat) : Wire := (annElemHead 32 a x tb).map (·.val)
/-- The byte-scale tail of an array element. -/
abbrev eTB (a : Ty) (x : Value a) : Wire := (annElemTail 32 a x).map (·.val)

theorem eHB_length (a : Ty) (x : Value a) (tb : Nat) : (eHB a x tb).length = elemWords a := by
  rw [List.length_map, annElemHead_scale, List.length_map, ← List.length_map (f := (·.val)),
    annElemHead_one, encElemHead_length]

theorem eTB_length (a : Ty) (x : Value a) : (eTB a x).length = (encElemTail a x).length := by
  rw [List.length_map, annElemTail_scale, List.length_map, ← List.length_map (f := (·.val)),
    annElemTail_one]

/-- Placement for an array element, given placement at the element type. -/
theorem decElemS_place_of (a : Ty)
    (IH : ∀ (v : Value a) (I : Input) (base ho tb : Nat) (s1 s2 : Wire),
      Fits a v → I.Full → 32 * I.words.length < 2 ^ 256 →
      I.words.drop (base + ho) = hB a v tb ++ s1 → I.words.drop (base + tb) = tB a v ++ s2 →
      decS a I (32 * base) (32 * ho) = .ok v)
    (x : Value a) (I : Input) (base ho tb : Nat) (s1 s2 : Wire)
    (hfit : Fits a x) (hI : I.Full) (hlen : 32 * I.words.length < 2 ^ 256)
    (hp : I.words.drop (base + ho) = eHB a x tb ++ s1)
    (ht : I.words.drop (base + tb) = eTB a x ++ s2) :
    decElemS a I (32 * base) (32 * ho) = .ok x := by
  cases a
  case pair a b =>
    by_cases hs : (isStatic a && isStatic b) = true
    · simp only [eHB, eTB, annElemHead, annElemTail, hs, if_true] at hp ht
      simp only [decElemS, hs, if_true]
      exact IH x I base ho tb s1 s2 hfit hI hlen hp ht
    · simp only [Bool.not_eq_true] at hs
      simp only [eHB, eTB, annElemHead, annElemTail, hs, Bool.false_eq_true, if_false,
        List.map_append, List.append_assoc] at hp ht
      have hp' : I.words.drop (base + ho) = natW (32 * tb) :: s1 := by simpa using hp
      have hlt0 := lt_length_of_drop (l := [natW (32 * tb)]) (by simpa using hp') (by simp)
      have hdyn : isStatic (Ty.pair a b) = false := by simpa [isStatic] using hs
      have hl : (hB (.pair a b) x (headWords a + headWords b)).length = headWords a + headWords b :=
        hB_length (.pair a b) x _
      have hlt : base + tb < I.words.length := lt_length_of_drop ht
        (by rw [hl]; exact headWords_pos_of_dynamic _ hdyn)
      have hoff : (rd I.words (base + ho)).toNat = 32 * tb := by
        rw [rd_of_drop hp', natW_toNat (by omega)]
      have htb : I.words.drop (base + tb + (headWords a + headWords b))
          = tB (.pair a b) x ++ s2 := by
        have hd := drop_add_length _ _ _ _ ht
        rw [hl] at hd
        exact hd
      have hx := IH x I (base + tb) 0 _ _ _ hfit hI hlen (by simpa using ht) htb
      simp only [Nat.mul_zero] at hx
      simp only [decElemS, hs, Bool.false_eq_true, if_false, readAt_ok hI hlt0, ok_bind, hoff,
        adv_ok hI (Nat.le_of_lt hlt), hx]
  all_goals
    simp only [eHB, eTB, annElemHead, annElemTail] at hp ht
    simp only [decElemS]
    exact IH x I base ho tb s1 s2 hfit hI hlen hp ht

mutual

/-- Placement lemma at the byte level: if the byte-scale head of `v` (tail
    cursor `tb`) sits at word `base + ho` and its tail at word `base + tb`, the
    strict decoder, reading at byte `32 × ho` from byte `32 × base`, succeeds
    with `v`. -/
theorem decS_place : ∀ (t : Ty) (v : Value t) (I : Input) (base ho tb : Nat) (s1 s2 : Wire),
    Fits t v → I.Full → 32 * I.words.length < 2 ^ 256 →
    I.words.drop (base + ho) = hB t v tb ++ s1 →
    I.words.drop (base + tb) = tB t v ++ s2 →
    decS t I (32 * base) (32 * ho) = .ok v
  | .unit => by intros; simp [decS]; rfl
  | .word => by
      intro v I base ho tb s1 s2 _ hI _ hp _
      have hp' : I.words.drop (base + ho) = v :: s1 := by simpa [hB, annHead] using hp
      have hlt := lt_length_of_drop (l := [v]) (by simpa using hp') (by simp)
      simp only [decS, readAt_ok hI hlt, rd_of_drop hp']
  | .bool => by
      intro v I base ho tb s1 s2 _ hI _ hp _
      have hp' : I.words.drop (base + ho) = (bif v then (1 : Word) else 0) :: s1 := by
        simpa [hB, annHead] using hp
      have hlt := lt_length_of_drop (l := [bif v then (1 : Word) else 0]) (by simpa using hp')
        (by simp)
      simp only [decS, readAt_ok hI hlt, rd_of_drop hp', ok_bind]
      cases v <;> rfl
  | .pair a b => by
      intro v I base ho tb s1 s2 hfit hI hlen hp ht
      simp only [hB, annHead, List.map_append, List.append_assoc] at hp
      simp only [tB, annTail, List.map_append, List.append_assoc] at ht
      have ha := decS_place a v.1 I base ho tb _ _ hfit.1 hI hlen hp ht
      have hpb := drop_add_length _ _ _ _ hp
      rw [List.length_map, annHead_scale, List.length_map, ← List.length_map (f := (·.val)),
        annHead_one, encHead_length, Nat.add_assoc] at hpb
      have htb := drop_add_length _ _ _ _ ht
      rw [List.length_map, annTail_scale, List.length_map, ← List.length_map (f := (·.val)),
        annTail_one, Nat.add_assoc] at htb
      have hb := decS_place b v.2 I base (ho + headWords a) _ _ _ hfit.2 hI hlen hpb htb
      simp only [decS, ha, ok_bind, ← Nat.mul_add, hb]; rfl
  | .sum a b => by
      intro v I base ho tb s1 s2 hfit hI hlen hp ht
      by_cases hs : (isStatic a && isStatic b) = true
      · have ⟨hsa, hsb⟩ : isStatic a = true ∧ isStatic b = true := by simpa using hs
        have hlt : base + ho < I.words.length :=
          lt_length_of_drop hp (by rw [hB_length]; simp only [headWords, hs, if_true]; omega)
        cases v with
        | inl x =>
            have hp' : I.words.drop (base + ho)
                = [(0 : Word)] ++ (hB a x tb ++ (List.replicate (padL a b) 0 ++ s1)) := by
              simpa [hB, annHead, hs] using hp
            have htag : rd I.words (base + ho) = 0 := rd_of_drop (by simpa using hp')
            have hpa := drop_add_length _ _ _ _ hp'
            have hx := decS_place a x I (base + ho) 1 tb _ (I.words.drop (base + ho + tb))
              hfit hI hlen (by simpa using hpa) (by rw [tB_nil_of_static a x hsa]; rfl)
            simp only [Nat.mul_one] at hx
            simp only [decS, hs, if_true, adv_ok hI (Nat.le_of_lt hlt), ok_bind,
              read_ok hI hlt, htag, hx]; rfl
        | inr y =>
            have hp' : I.words.drop (base + ho)
                = [(1 : Word)] ++ (hB b y tb ++ (List.replicate (padR a b) 0 ++ s1)) := by
              simpa [hB, annHead, hs] using hp
            have htag : rd I.words (base + ho) = 1 := rd_of_drop (by simpa using hp')
            have hpb := drop_add_length _ _ _ _ hp'
            have hy := decS_place b y I (base + ho) 1 tb _ (I.words.drop (base + ho + tb))
              hfit hI hlen (by simpa using hpb) (by rw [tB_nil_of_static b y hsb]; rfl)
            simp only [Nat.mul_one] at hy
            simp only [decS, hs, if_true, adv_ok hI (Nat.le_of_lt hlt), ok_bind,
              read_ok hI hlt, htag, hy]; rfl
      · simp only [Bool.not_eq_true] at hs
        cases v with
        | inl x =>
            have hp' : I.words.drop (base + ho) = natW (32 * tb) :: s1 := by
              simpa [hB, annHead, hs] using hp
            have hlt0 := lt_length_of_drop (l := [natW (32 * tb)]) (by simpa using hp') (by simp)
            have ht' : I.words.drop (base + tb)
                = ([(0 : Word)] ++ hB a x (1 + max (headWords a) (headWords b))
                    ++ List.replicate (padL a b) 0) ++ (tB a x ++ s2) := by
              simpa [hB, tB, annTail, hs] using ht
            have hlt : base + tb < I.words.length := lt_length_of_drop ht' (by simp)
            have hoff : (rd I.words (base + ho)).toNat = 32 * tb := by
              rw [rd_of_drop hp', natW_toNat (by omega)]
            have htag : rd I.words (base + tb) = 0 := rd_of_drop (by simpa using ht')
            have hpa : I.words.drop (base + tb + 1)
                = hB a x (1 + max (headWords a) (headWords b))
                  ++ (List.replicate (padL a b) 0 ++ (tB a x ++ s2)) := by
              have hd := drop_add_length _ (base + tb) [(0 : Word)] _ (by simpa using ht')
              simpa using hd
            have hta : I.words.drop (base + tb + (1 + max (headWords a) (headWords b)))
                = tB a x ++ s2 := by
              have hd := drop_add_length _ (base + tb) _ _ ht'
              have hl : ([(0 : Word)] ++ hB a x (1 + max (headWords a) (headWords b))
                  ++ List.replicate (padL a b) 0).length = 1 + max (headWords a) (headWords b) := by
                simp only [List.length_append, hB_length, List.length_replicate, padL,
                  List.length_singleton]
                omega
              rwa [hl] at hd
            have hx := decS_place a x I (base + tb) 1 _ _ _ hfit hI hlen hpa hta
            simp only [Nat.mul_one] at hx
            simp only [decS, hs, Bool.false_eq_true, if_false, readAt_ok hI hlt0, ok_bind, hoff,
              adv_ok hI (Nat.le_of_lt hlt), read_ok hI hlt, htag, hx]; rfl
        | inr y =>
            have hp' : I.words.drop (base + ho) = natW (32 * tb) :: s1 := by
              simpa [hB, annHead, hs] using hp
            have hlt0 := lt_length_of_drop (l := [natW (32 * tb)]) (by simpa using hp') (by simp)
            have ht' : I.words.drop (base + tb)
                = ([(1 : Word)] ++ hB b y (1 + max (headWords a) (headWords b))
                    ++ List.replicate (padR a b) 0) ++ (tB b y ++ s2) := by
              simpa [hB, tB, annTail, hs] using ht
            have hlt : base + tb < I.words.length := lt_length_of_drop ht' (by simp)
            have hoff : (rd I.words (base + ho)).toNat = 32 * tb := by
              rw [rd_of_drop hp', natW_toNat (by omega)]
            have htag : rd I.words (base + tb) = 1 := rd_of_drop (by simpa using ht')
            have hpb : I.words.drop (base + tb + 1)
                = hB b y (1 + max (headWords a) (headWords b))
                  ++ (List.replicate (padR a b) 0 ++ (tB b y ++ s2)) := by
              have hd := drop_add_length _ (base + tb) [(1 : Word)] _ (by simpa using ht')
              simpa using hd
            have htb : I.words.drop (base + tb + (1 + max (headWords a) (headWords b)))
                = tB b y ++ s2 := by
              have hd := drop_add_length _ (base + tb) _ _ ht'
              have hl : ([(1 : Word)] ++ hB b y (1 + max (headWords a) (headWords b))
                  ++ List.replicate (padR a b) 0).length = 1 + max (headWords a) (headWords b) := by
                simp only [List.length_append, hB_length, List.length_replicate, padR,
                  List.length_singleton]
                omega
              rwa [hl] at hd
            have hy := decS_place b y I (base + tb) 1 _ _ _ hfit hI hlen hpb htb
            simp only [Nat.mul_one] at hy
            simp only [decS, hs, Bool.false_eq_true, if_false, readAt_ok hI hlt0, ok_bind, hoff,
              adv_ok hI (Nat.le_of_lt hlt), read_ok hI hlt, htag, hy]; rfl
  | .tup a => by
      intro v I base ho tb s1 s2 hfit hI hlen hp ht
      by_cases hsa : isStatic a = true
      · have hp' : I.words.drop (base + ho) = hB a v tb ++ s1 := by
          simpa [hB, annHead, hsa] using hp
        have ht' : I.words.drop (base + tb) = tB a v ++ s2 := by
          rw [tB_nil_of_static a v hsa]; simpa [tB, annTail, hsa] using ht
        simp only [decS, hsa, if_true]
        exact decS_place a v I base ho tb s1 s2 hfit hI hlen hp' ht'
      · simp only [Bool.not_eq_true] at hsa
        have hp' : I.words.drop (base + ho) = natW (32 * tb) :: s1 := by
          simpa [hB, annHead, hsa] using hp
        have hlt0 := lt_length_of_drop (l := [natW (32 * tb)]) (by simpa using hp') (by simp)
        have ht' : I.words.drop (base + tb) = hB a v (headWords a) ++ (tB a v ++ s2) := by
          simpa [hB, tB, annTail, hsa] using ht
        have hlt : base + tb < I.words.length :=
          lt_length_of_drop ht' (by rw [hB_length]; exact headWords_pos_of_dynamic a hsa)
        have hoff : (rd I.words (base + ho)).toNat = 32 * tb := by
          rw [rd_of_drop hp', natW_toNat (by omega)]
        have hta : I.words.drop (base + tb + headWords a) = tB a v ++ s2 := by
          have hd := drop_add_length _ _ _ _ ht'
          rwa [hB_length] at hd
        have hx := decS_place a v I (base + tb) 0 (headWords a) _ _ hfit hI hlen
          (by simpa using ht') hta
        simp only [Nat.mul_zero] at hx
        simp only [decS, hsa, Bool.false_eq_true, if_false, readAt_ok hI hlt0, ok_bind, hoff,
          adv_ok hI (Nat.le_of_lt hlt), hx]
  | .array a => by
      intro v I base ho tb s1 s2 hfit hI hlen hp ht
      have hseq : ∀ (xs : List (Value a)) (region i tb' : Nat) (s1' s2' : Wire),
          (∀ x ∈ xs, Fits a x) →
          I.words.drop (region + i * elemWords a) = (annHeadSeq 32 a xs tb').map (·.val) ++ s1' →
          I.words.drop (region + tb') = (annTailSeq 32 a xs).map (·.val) ++ s2' →
          decSeqS a I (32 * region) xs.length i = .ok xs := by
        intro xs
        induction xs with
        | nil => intros; simp [decSeqS]; rfl
        | cons x xs ih =>
            intro region i tb' s1' s2' hf hph hpt
            simp only [annHeadSeq, List.map_append, List.append_assoc] at hph
            simp only [annTailSeq, List.map_append, List.append_assoc] at hpt
            have hx := decElemS_place_of a (decS_place a) x I region (i * elemWords a) tb' _ _
              (hf x (by simp)) hI hlen hph hpt
            have hph2 := drop_add_length _ _ _ _ hph
            rw [eHB_length, Nat.add_assoc, ← Nat.succ_mul] at hph2
            have hpt2 := drop_add_length _ _ _ _ hpt
            rw [eTB_length, Nat.add_assoc] at hpt2
            have hrest := ih region (i + 1) _ _ _ (fun y hy => hf y (by simp [hy])) hph2 hpt2
            have hmul : i * (32 * elemWords a) = 32 * (i * elemWords a) := by
              rw [Nat.mul_left_comm]
            simp only [List.length_cons, decSeqS, hmul, hx, ok_bind, hrest]; rfl
      have hp' : I.words.drop (base + ho) = natW (32 * tb) :: s1 := by
        simpa [hB, annHead] using hp
      have hlt0 := lt_length_of_drop (l := [natW (32 * tb)]) (by simpa using hp') (by simp)
      have ht' : I.words.drop (base + tb) = [natW v.length]
          ++ ((annHeadSeq 32 a v (v.length * elemWords a)).map (·.val)
            ++ ((annTailSeq 32 a v).map (·.val) ++ s2)) := by
        simpa [tB, annTail] using ht
      have hlt : base + tb < I.words.length := lt_length_of_drop ht' (by simp)
      have hoff : (rd I.words (base + ho)).toNat = 32 * tb := by
        rw [rd_of_drop hp', natW_toNat (by omega)]
      have hlenw : (rd I.words (base + tb)).toNat = v.length := by
        rw [rd_of_drop (by simpa using ht'), natW_toNat (Nat.lt_trans hfit.1 (by decide))]
      have hh := drop_add_length _ _ _ _ ht'
      simp only [List.length_singleton] at hh
      have hle := le_length_of_drop hh (by omega)
      rw [List.length_map, annHeadSeq32_length] at hle
      have ht2 := drop_add_length _ _ _ _ hh
      rw [List.length_map, annHeadSeq32_length] at ht2
      have hx := hseq v (base + tb + 1) 0 _ _ _ hfit.2 (by simpa using hh) ht2
      -- the std's checks on the length
      have hstride : ¬ (32 * elemWords a > 0 ∧ v.length > maxWord / (32 * elemWords a)) := by
        intro ⟨hpos, hgt⟩
        have : v.length * (32 * elemWords a) ≤ maxWord := by
          have : 32 * (v.length * elemWords a) < 2 ^ 256 := by omega
          simp only [maxWord]
          rw [Nat.mul_left_comm]; omega
        exact absurd ((Nat.le_div_iff_mul_le hpos).mpr this) (by omega)
      have hsmall : v.length < maxWord / 32 := by
        have : maxWord / 32 = 2 ^ 251 - 1 := by decide
        rw [this]; exact hfit.1
      have hadv : I.adv (32 * (base + tb + 1)) (v.length * (32 * elemWords a))
          = .ok (32 * (base + tb + 1 + v.length * elemWords a)) := by
        rw [Nat.mul_left_comm]; exact adv_ok hI hle
      simp only [decS, readAt_ok hI hlt0, ok_bind, hoff, adv_ok hI (Nat.le_of_lt hlt),
        read_ok hI hlt, hlenw, adv_ok_one hI hlt, hadv, hx]
      simp only [hsmall]
      simp
      intro hpos hgt
      exact absurd ⟨by omega, hgt⟩ hstride
  | .enum n t cs => by
      intro v I base ho tb s1 s2 hfit hI hlen hp ht
      have hf := Fits_enum hfit
      by_cases hs : (isStatic t && isStaticC cs) = true
      · have ⟨hst, hsc⟩ : isStatic t = true ∧ isStaticC cs = true := by simpa using hs
        have hp' : I.words.drop (base + ho)
            = [armTag n t cs v] ++ ((annArmHead 32 t cs v tb).map (·.val)
              ++ (List.replicate (max (headWords t) (maxArmC cs) - armWords t cs v) 0 ++ s1)) := by
          simpa [hB, annHead, hs] using hp
        have hlt : base + ho < I.words.length := lt_length_of_drop hp' (by simp)
        have htag : rd I.words (base + ho) = armTag n t cs v := rd_of_drop (by simpa using hp')
        have hpa := drop_add_length _ _ _ _ hp'
        have hx := decArmS_place n t cs v I (base + ho) tb _ (I.words.drop (base + ho + tb))
          hf.1 hf.2 hI hlen (by simpa using hpa) (by rw [aTB_nil_of_static t cs v hst hsc]; rfl)
        simp only [decS, hs, if_true, adv_ok hI (Nat.le_of_lt hlt), ok_bind, read_ok hI hlt,
          htag, hx]
      · simp only [Bool.not_eq_true] at hs
        have hp' : I.words.drop (base + ho) = natW (32 * tb) :: s1 := by
          simpa [hB, annHead, hs] using hp
        have hlt0 := lt_length_of_drop (l := [natW (32 * tb)]) (by simpa using hp') (by simp)
        have ht' : I.words.drop (base + tb)
            = ([armTag n t cs v]
                ++ (annArmHead 32 t cs v (1 + max (headWords t) (maxArmC cs))).map (·.val)
                ++ List.replicate (max (headWords t) (maxArmC cs) - armWords t cs v) 0)
              ++ ((annArmTail 32 t cs v).map (·.val) ++ s2) := by
          simpa [tB, annTail, hs] using ht
        have hlt : base + tb < I.words.length := lt_length_of_drop ht' (by simp)
        have hoff : (rd I.words (base + ho)).toNat = 32 * tb := by
          rw [rd_of_drop hp', natW_toNat (by omega)]
        have htag : rd I.words (base + tb) = armTag n t cs v := rd_of_drop (by simpa using ht')
        have hpa : I.words.drop (base + tb + 1)
            = (annArmHead 32 t cs v (1 + max (headWords t) (maxArmC cs))).map (·.val)
              ++ (List.replicate (max (headWords t) (maxArmC cs) - armWords t cs v) 0
                ++ ((annArmTail 32 t cs v).map (·.val) ++ s2)) := by
          have hd := drop_add_length _ (base + tb) [armTag n t cs v] _ (by simpa using ht')
          simpa using hd
        have hta : I.words.drop (base + tb + (1 + max (headWords t) (maxArmC cs)))
            = (annArmTail 32 t cs v).map (·.val) ++ s2 := by
          have hd := drop_add_length _ (base + tb) _ _ ht'
          have hl : ([armTag n t cs v]
              ++ (annArmHead 32 t cs v (1 + max (headWords t) (maxArmC cs))).map (fun c : Cell => c.val)
              ++ List.replicate (max (headWords t) (maxArmC cs) - armWords t cs v) 0).length
              = 1 + max (headWords t) (maxArmC cs) := by
            have := armWords_le_maxArm t cs v
            simp only [List.length_append, aHB_length, List.length_replicate,
              List.length_singleton]
            omega
          rwa [hl] at hd
        have hx := decArmS_place n t cs v I (base + tb) _ _ _ hf.1 hf.2 hI hlen hpa hta
        simp only [decS, hs, Bool.false_eq_true, if_false, readAt_ok hI hlt0, ok_bind, hoff,
          adv_ok hI (Nat.le_of_lt hlt), read_ok hI hlt, htag, hx]
  termination_by t => (sizeOf t, 1)

/-- Placement for the selected payload of an enum whose start is at word
    `base`: the derived decoder, given the written tag, recovers it. -/
theorem decArmS_place : ∀ (n : String) (t : Ty) (cs : Ctors) (v : Value t ⊕ ValueC cs)
    (I : Input) (base tb : Nat) (s1 s2 : Wire),
    (ctorTag n t :: tagsC cs).Nodup → FitsArm t cs v → I.Full → 32 * I.words.length < 2 ^ 256 →
    I.words.drop (base + 1) = (annArmHead 32 t cs v tb).map (·.val) ++ s1 →
    I.words.drop (base + tb) = (annArmTail 32 t cs v).map (·.val) ++ s2 →
    decArmS n t cs I (32 * base) (armTag n t cs v) = .ok v
  | n, t, .cons m u cs, .inl x => by
      intro I base tb s1 s2 _ hf hI hlen hp ht
      rw [annArmHead.eq_1] at hp
      rw [annArmTail.eq_1] at ht
      have hx := decS_place t x I base 1 tb s1 s2 (FitsArm_inl hf) hI hlen hp ht
      simp only [Nat.mul_one] at hx
      simp [armTag, decArmS, hx]; rfl
  | n, t, .cons m u cs, .inr y => by
      intro I base tb s1 s2 hnd hf hI hlen hp ht
      have hne := armTag_inr_ne (y := y) hnd
      have hnd' : (ctorTag m u :: tagsC cs).Nodup := by
        simpa [tagsC] using (List.nodup_cons.mp hnd).2
      rw [annArmHead.eq_2] at hp
      rw [annArmTail.eq_2] at ht
      have hy := decArmS_place m u cs y I base tb s1 s2 hnd' (FitsArm_cons_inr hf) hI hlen hp ht
      simp only [armTag] at hne hy ⊢
      simp [decArmS, hne, hy]; rfl
  | n, t, .last m u, .inl x => by
      intro I base tb s1 s2 _ hf hI hlen hp ht
      rw [annArmHead.eq_1] at hp
      rw [annArmTail.eq_1] at ht
      have hx := decS_place t x I base 1 tb s1 s2 (FitsArm_inl hf) hI hlen hp ht
      simp only [Nat.mul_one] at hx
      simp [armTag, decArmS, hx]; rfl
  | n, t, .last m u, .inr y => by
      intro I base tb s1 s2 hnd hf hI hlen hp ht
      have hne := armTag_inr_ne (y := y) hnd
      rw [annArmHead.eq_3] at hp
      rw [annArmTail.eq_3] at ht
      have hy := decS_place u y I base 1 tb s1 s2 (FitsArm_last_inr hf) hI hlen hp ht
      simp only [Nat.mul_one] at hy
      simp only [armTag] at hne ⊢
      simp [decArmS, hne, hy]; rfl
  termination_by _ t cs => (sizeOf t + sizeOf cs, 0)
  decreasing_by all_goals simp_wf; all_goals first | omega | (have := Ctors.sizeOf_pos ‹Ctors›; omega)

end

/-! ### The canonical encoding decodes -/

/-- **The strict decoder accepts the canonical encoding.** Given the round
    trip's side conditions (`Fits`: array lengths below solcore-rs's bound,
    distinct constructor tags) and an encoding whose byte length fits in a word
    (so that no byte offset wraps), solcore-rs's decoder, run on the byte-level
    encoding of `v` as a public method's arguments, succeeds with `v`. -/
theorem decStrict_encodeBytes (t : Ty) (v : Value t) (hfit : Fits t v)
    (hlen : 32 * (encode t v).length < 2 ^ 256) :
    decStrict t (Input.ofWire (encodeBytes t v)) = .ok v := by
  have hwl : (encodeBytes t v).length = (encode t v).length := encodeBytes_length t v
  have hsplit : encodeBytes t v = hB t v (headWords t) ++ tB t v := by
    simp [encodeBytes, encodeAnn]
  have hI : (Input.ofWire (encodeBytes t v)).Full := rfl
  have hlen' : 32 * (Input.ofWire (encodeBytes t v)).words.length < 2 ^ 256 := by
    simp only [Input.ofWire, hwl]; exact hlen
  have hhead : 32 * headWords t ≤ (Input.ofWire (encodeBytes t v)).size := by
    have := congrArg List.length hsplit
    simp only [List.length_append, hB_length] at this
    simp only [Input.ofWire]; omega
  have hp : (Input.ofWire (encodeBytes t v)).words.drop (0 + 0)
      = hB t v (headWords t) ++ tB t v := by simpa [Input.ofWire] using hsplit
  have ht : (Input.ofWire (encodeBytes t v)).words.drop (0 + headWords t) = tB t v ++ [] := by
    have := drop_add_length _ _ _ _ hp
    rw [hB_length] at this
    simpa using this
  have h := decS_place t v _ 0 0 (headWords t) _ _ hfit hI hlen' hp ht
  simp only [decStrict, Nat.not_lt.mpr hhead, if_false]
  simpa using h

/-! ### Stability: re-encoding a decoded value

What `decStrict` returns is a value the round trip applies to: decoding the
re-encoding of a decoded value gives it back (`decStrict_stable`). The side
conditions come from the decoder itself, except two. The constructor tags of
the type's enums must be distinct (`TagsOK`), a property of the type. And the
re-encoding must fit: since offsets in the input may be shared (several heads
pointing at one tail), the decoded value's canonical encoding can be much larger
than the input, so its size is a hypothesis.
-/

mutual

/-- Every enum in the type has pairwise-distinct constructor tags. -/
def TagsOK : Ty → Prop
  | .unit | .word | .bool => True
  | .pair a b | .sum a b => TagsOK a ∧ TagsOK b
  | .tup a | .array a => TagsOK a
  | .enum n t cs => (ctorTag n t :: tagsC cs).Nodup ∧ TagsOK t ∧ TagsOKC cs

/-- `TagsOK` for the payloads of the remaining constructors. -/
def TagsOKC : Ctors → Prop
  | .last _ u => TagsOK u
  | .cons _ u cs => TagsOK u ∧ TagsOKC cs

end

theorem bind_ok {α β} {x : Dec α} {f : α → Dec β} {b : β} (h : (x >>= f) = .ok b) :
    ∃ a, x = .ok a ∧ f a = .ok b := by
  cases x with
  | error e => cases h
  | ok a => exact ⟨a, rfl, h⟩

theorem pure_ok {α} {a b : α} (h : (pure a : Dec α) = .ok b) : a = b := by
  cases h; rfl

theorem throw_ok {α} {e : AbiError} {b : α} (h : (throw e : Dec α) = .ok b) : False := by
  cases h

theorem decElemS_fits_of (a : Ty)
    (IH : ∀ (I : Input) (p ho : Nat) (v : Value a), TagsOK a → decS a I p ho = .ok v → Fits a v)
    (I : Input) (p ho : Nat) (v : Value a) (hok : TagsOK a) (h : decElemS a I p ho = .ok v) :
    Fits a v := by
  cases a
  case pair a b =>
    simp only [decElemS] at h
    split at h
    · exact IH I p ho v hok h
    · obtain ⟨o, -, h⟩ := bind_ok h
      obtain ⟨q, -, h⟩ := bind_ok h
      exact IH I _ _ v hok h
  all_goals (simp only [decElemS] at h; exact IH I p ho v hok h)

mutual

/-- What the strict decoder returns satisfies the round trip's side
    conditions, given distinct tags in the type. -/
theorem decS_fits : ∀ (t : Ty) (I : Input) (p ho : Nat) (v : Value t),
    TagsOK t → decS t I p ho = .ok v → Fits t v
  | .unit => by intros; trivial
  | .word => by intros; trivial
  | .bool => by intros; trivial
  | .pair a b => by
      intro I p ho v hok h
      simp only [decS] at h
      obtain ⟨x, hx, h⟩ := bind_ok h
      obtain ⟨y, hy, h⟩ := bind_ok h
      cases pure_ok h
      exact ⟨decS_fits a I _ _ x hok.1 hx, decS_fits b I _ _ y hok.2 hy⟩
  | .sum a b => by
      intro I p ho v hok h
      simp only [decS] at h
      have body : ∀ (s : Nat) (v : Value (.sum a b)),
          (do
            let tag ← I.read s
            if tag = 0 then do
                let x ← decS a I s 32
                pure (Sum.inl x)
              else do
                let y ← decS b I s 32
                pure (Sum.inr y) : Dec (Value (.sum a b))) = .ok v → Fits (.sum a b) v := by
        intro s v h
        obtain ⟨tag, -, h⟩ := bind_ok h
        split at h
        · obtain ⟨x, hx, h⟩ := bind_ok h
          cases pure_ok h
          exact decS_fits a I _ _ x hok.1 hx
        · obtain ⟨y, hy, h⟩ := bind_ok h
          cases pure_ok h
          exact decS_fits b I _ _ y hok.2 hy
      split at h
      · obtain ⟨s, -, h⟩ := bind_ok h
        exact body s v h
      · obtain ⟨o, -, h⟩ := bind_ok h
        obtain ⟨s, -, h⟩ := bind_ok h
        exact body s v h
  | .tup a => by
      intro I p ho v hok h
      simp only [decS] at h
      split at h
      · exact decS_fits a I _ _ v hok h
      · obtain ⟨o, -, h⟩ := bind_ok h
        obtain ⟨q, -, h⟩ := bind_ok h
        exact decS_fits a I _ _ v hok h
  | .array a => by
      intro I p ho v hok h
      have hseq : ∀ (k : Nat) (el i : Nat) (xs : List (Value a)),
          decSeqS a I el k i = .ok xs → xs.length = k ∧ ∀ x ∈ xs, Fits a x := by
        intro k
        induction k with
        | zero => intro el i xs h; simp only [decSeqS] at h; cases pure_ok h; simp
        | succ k ih =>
            intro el i xs h
            simp only [decSeqS] at h
            obtain ⟨x, hx, h⟩ := bind_ok h
            obtain ⟨xs', hxs', h⟩ := bind_ok h
            cases pure_ok h
            obtain ⟨hl, hf⟩ := ih el (i + 1) xs' hxs'
            refine ⟨by simp [hl], ?_⟩
            intro y hy
            simp only [List.mem_cons] at hy
            rcases hy with rfl | hy
            · exact decElemS_fits_of a (decS_fits a) I _ _ y hok hx
            · exact hf y hy
      simp only [decS] at h
      obtain ⟨o, -, h⟩ := bind_ok h
      obtain ⟨arr, -, h⟩ := bind_ok h
      obtain ⟨lenw, -, h⟩ := bind_ok h
      obtain ⟨el, -, h⟩ := bind_ok h
      have tail : ∀ (h : (do
            let _ ← I.adv el (lenw.toNat * (32 * elemWords a))
            if (!decide (lenw.toNat < maxWord / 32)) = true then do
                throw AbiError.truncated
                decSeqS a I el lenw.toNat 0
              else decSeqS a I el lenw.toNat 0 : Dec (List (Value a))) = .ok v),
          Fits (.array a) v := by
        intro h
        obtain ⟨u, -, h⟩ := bind_ok h
        split at h
        · obtain ⟨_, hc, _⟩ := bind_ok h
          exact (throw_ok hc).elim
        · rename_i hsmall
          obtain ⟨hl, hf⟩ := hseq _ _ _ v h
          refine ⟨?_, hf⟩
          have : maxWord / 32 = 2 ^ 251 - 1 := by decide
          rw [hl]
          have hlt : lenw.toNat < maxWord / 32 := by simpa using hsmall
          omega
      split at h
      · obtain ⟨_, hc, _⟩ := bind_ok h
        exact (throw_ok hc).elim
      · exact tail h
  | .enum n t cs => by
      intro I p ho v hok h
      simp only [decS] at h
      have harm : FitsArm t cs v := by
        split at h
        · obtain ⟨s, -, h⟩ := bind_ok h
          obtain ⟨tag, -, h⟩ := bind_ok h
          exact decArmS_fits n t cs I s tag v hok.2.1 hok.2.2 h
        · obtain ⟨o, -, h⟩ := bind_ok h
          obtain ⟨s, -, h⟩ := bind_ok h
          obtain ⟨tag, -, h⟩ := bind_ok h
          exact decArmS_fits n t cs I s tag v hok.2.1 hok.2.2 h
      cases v with
      | inl x => exact ⟨hok.1, harm⟩
      | inr y => exact ⟨hok.1, harm⟩
  termination_by t => (sizeOf t, 1)

theorem decArmS_fits : ∀ (n : String) (t : Ty) (cs : Ctors) (I : Input) (s : Nat) (tag : Word)
    (v : Value t ⊕ ValueC cs),
    TagsOK t → TagsOKC cs → decArmS n t cs I s tag = .ok v → FitsArm t cs v
  | n, t, .cons m u cs => by
      intro I s tag v ht hc h
      simp only [decArmS] at h
      split at h
      · obtain ⟨x, hx, h⟩ := bind_ok h
        cases pure_ok h
        exact decS_fits t I _ _ x ht hx
      · obtain ⟨y, hy, h⟩ := bind_ok h
        cases pure_ok h
        have := decArmS_fits m u cs I s tag y hc.1 hc.2 hy
        cases y with
        | inl x => exact this
        | inr z => exact this
  | n, t, .last m u => by
      intro I s tag v ht hc h
      simp only [decArmS] at h
      split at h
      · obtain ⟨x, hx, h⟩ := bind_ok h
        cases pure_ok h
        exact decS_fits t I _ _ x ht hx
      · split at h
        · obtain ⟨y, hy, h⟩ := bind_ok h
          cases pure_ok h
          exact decS_fits u I _ _ y hc hy
        · exact (throw_ok h).elim
  termination_by _ t cs => (sizeOf t + sizeOf cs, 0)
  decreasing_by all_goals simp_wf; all_goals first | omega | (have := Ctors.sizeOf_pos ‹Ctors›; omega)

end

theorem decStrict_fits {t : Ty} {I : Input} {v : Value t} (htags : TagsOK t)
    (h : decStrict t I = .ok v) : Fits t v := by
  simp only [decStrict] at h
  split at h
  · exact (throw_ok h).elim
  · exact decS_fits t I 0 0 v htags h

/-- **Stability.** A value the strict decoder returns, from any input, is
    re-encoded canonically into input the decoder accepts, and decodes back to
    the same value: `decStrict ∘ encodeBytes` is the identity on the decoder's
    results. Hypotheses: distinct constructor tags in the type, and a
    re-encoding whose byte length fits in a word. -/
theorem decStrict_stable {t : Ty} {I : Input} {v : Value t} (htags : TagsOK t)
    (h : decStrict t I = .ok v) (hlen : 32 * (encode t v).length < 2 ^ 256) :
    decStrict t (Input.ofWire (encodeBytes t v)) = .ok v :=
  decStrict_encodeBytes t v (decStrict_fits htags h) hlen

/-! ### Refinement: the strict decoder only adds checks

When `decStrict` succeeds, the lenient byte-level decoder `decLax` returns the
same value: every read the strict decoder makes succeeds with the word
`decLax` reads, every advance lands where `decLax` computes, a bool that passes
the check (`0`/`1`) is the same under both readings, and the tag that selects a
constructor in the strict decoder selects the same one in the lenient decoder.
-/

theorem read_inv {I : Input} {p : Nat} {w : Word} (h : I.read p = .ok w) : w = I.wordAt p := by
  simp only [Input.read] at h
  split at h
  · cases h; rfl
  · cases h

theorem adv_inv {I : Input} {p off q : Nat} (h : I.adv p off = .ok q) : q = p + off := by
  simp only [Input.adv] at h
  split at h
  · cases h; rfl
  · cases h

theorem readAt_inv {I : Input} {p ho : Nat} {w : Word} (h : I.readAt p ho = .ok w) :
    w = I.wordAt (p + ho) := by
  simp only [Input.readAt] at h
  obtain ⟨q, hq, h⟩ := bind_ok h
  rw [read_inv h, adv_inv hq]

theorem decElemS_refines_of (a : Ty)
    (IH : ∀ (I : Input) (p ho : Nat) (v : Value a), decS a I p ho = .ok v → decLax a I p ho = v)
    (I : Input) (p ho : Nat) (v : Value a) (h : decElemS a I p ho = .ok v) :
    decElemLax a I p ho = v := by
  cases a
  case pair a b =>
    simp only [decElemS] at h
    split at h
    · rename_i hs
      simp only [decElemLax, hs, if_true]
      exact IH I p ho v h
    · rename_i hs
      obtain ⟨o, ho', h⟩ := bind_ok h
      obtain ⟨q, hq, h⟩ := bind_ok h
      simp only [decElemLax, hs, Bool.false_eq_true, if_false]
      rw [← readAt_inv ho', ← adv_inv hq]
      exact IH I _ _ v h
  all_goals (simp only [decElemS] at h; simp only [decElemLax]; try exact IH I p ho v h)

mutual

theorem decS_refines : ∀ (t : Ty) (I : Input) (p ho : Nat) (v : Value t),
    decS t I p ho = .ok v → decLax t I p ho = v
  | .unit => by intros; rfl
  | .word => by
      intro I p ho v h
      simp only [decS] at h
      simp only [decLax, readAt_inv h]
  | .bool => by
      intro I p ho v h
      simp only [decS] at h
      obtain ⟨w, hw, h⟩ := bind_ok h
      split at h
      · rename_i hle
        cases pure_ok h
        simp only [decLax, ← readAt_inv hw]
        rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hle with h0 | h1
        · have : w = 0 := BitVec.eq_of_toNat_eq (by simpa using h0)
          subst this; rfl
        · have : w = 1 := BitVec.eq_of_toNat_eq (by simpa using h1)
          subst this; rfl
      · exact (throw_ok h).elim
  | .pair a b => by
      intro I p ho v h
      simp only [decS] at h
      obtain ⟨x, hx, h⟩ := bind_ok h
      obtain ⟨y, hy, h⟩ := bind_ok h
      cases pure_ok h
      simp only [decLax, decS_refines a I _ _ x hx, decS_refines b I _ _ y hy]
  | .sum a b => by
      intro I p ho v h
      simp only [decS] at h
      have body : ∀ (s : Nat), s = (if isStatic a && isStatic b then p + ho
            else p + (I.wordAt (p + ho)).toNat) →
          (do
            let tag ← I.read s
            if tag = 0 then do
                let x ← decS a I s 32
                pure (Sum.inl x)
              else do
                let y ← decS b I s 32
                pure (Sum.inr y) : Dec (Value (.sum a b))) = .ok v →
          decLax (.sum a b) I p ho = v := by
        intro s hs h
        obtain ⟨tag, htag, h⟩ := bind_ok h
        rw [read_inv htag] at h
        simp only [decLax, ← hs]
        split at h
        · rename_i h0
          obtain ⟨x, hx, h⟩ := bind_ok h
          cases pure_ok h
          simp only [h0, if_true, decS_refines a I _ _ x hx]
        · rename_i h0
          obtain ⟨y, hy, h⟩ := bind_ok h
          cases pure_ok h
          simp only [h0, if_false, decS_refines b I _ _ y hy]
      split at h
      · rename_i hs
        obtain ⟨s, hsv, h⟩ := bind_ok h
        exact body s (by rw [adv_inv hsv, if_pos hs]) h
      · rename_i hs
        obtain ⟨o, ho', h⟩ := bind_ok h
        obtain ⟨s, hsv, h⟩ := bind_ok h
        exact body s (by rw [adv_inv hsv, if_neg hs, readAt_inv ho']) h
  | .tup a => by
      intro I p ho v h
      simp only [decS] at h
      split at h
      · rename_i hs
        simp only [decLax, hs, if_true]
        exact decS_refines a I _ _ v h
      · rename_i hs
        obtain ⟨o, ho', h⟩ := bind_ok h
        obtain ⟨q, hq, h⟩ := bind_ok h
        simp only [decLax, hs, Bool.false_eq_true, if_false]
        rw [← readAt_inv ho', ← adv_inv hq]
        exact decS_refines a I _ _ v h
  | .array a => by
      intro I p ho v h
      have hseq : ∀ (k el i : Nat) (xs : List (Value a)),
          decSeqS a I el k i = .ok xs → decSeqLax a I el k i = xs := by
        intro k
        induction k with
        | zero => intro el i xs h; simp only [decSeqS] at h; cases pure_ok h; simp [decSeqLax]
        | succ k ih =>
            intro el i xs h
            simp only [decSeqS] at h
            obtain ⟨x, hx, h⟩ := bind_ok h
            obtain ⟨xs', hxs', h⟩ := bind_ok h
            cases pure_ok h
            simp only [decSeqLax, decElemS_refines_of a (decS_refines a) I _ _ x hx,
              ih el (i + 1) xs' hxs']
      simp only [decS] at h
      obtain ⟨o, ho', h⟩ := bind_ok h
      obtain ⟨arr, harr, h⟩ := bind_ok h
      obtain ⟨lenw, hlenw, h⟩ := bind_ok h
      obtain ⟨el, hel, h⟩ := bind_ok h
      have hv : decSeqS a I el lenw.toNat 0 = .ok v := by
        split at h
        · obtain ⟨_, hc, _⟩ := bind_ok h
          exact (throw_ok hc).elim
        · obtain ⟨u, -, h⟩ := bind_ok h
          split at h
          · obtain ⟨_, hc, _⟩ := bind_ok h
            exact (throw_ok hc).elim
          · exact h
      simp only [decLax]
      rw [← readAt_inv ho', ← adv_inv harr, ← read_inv hlenw, ← adv_inv hel]
      exact hseq _ _ _ v hv
  | .enum n t cs => by
      intro I p ho v h
      simp only [decS] at h
      have body : ∀ (s : Nat), s = (if isStatic t && isStaticC cs then p + ho
            else p + (I.wordAt (p + ho)).toNat) →
          (do
            let tag ← I.read s
            decArmS n t cs I s tag : Dec (Value (.enum n t cs))) = .ok v →
          decLax (.enum n t cs) I p ho = v := by
        intro s hs h
        obtain ⟨tag, htag, h⟩ := bind_ok h
        simp only [decLax, ← hs, ← read_inv htag]
        exact decArmS_refines n t cs I s tag v h
      split at h
      · rename_i hs
        obtain ⟨s, hsv, h⟩ := bind_ok h
        exact body s (by rw [adv_inv hsv, if_pos hs]) h
      · rename_i hs
        obtain ⟨o, ho', h⟩ := bind_ok h
        obtain ⟨s, hsv, h⟩ := bind_ok h
        exact body s (by rw [adv_inv hsv, if_neg hs, readAt_inv ho']) h
  termination_by t => (sizeOf t, 1)

theorem decArmS_refines : ∀ (n : String) (t : Ty) (cs : Ctors) (I : Input) (s : Nat) (tag : Word)
    (v : Value t ⊕ ValueC cs),
    decArmS n t cs I s tag = .ok v → decArmLax n t cs I s tag = v
  | n, t, .cons m u cs => by
      intro I s tag v h
      simp only [decArmS] at h
      split at h
      · rename_i heq
        obtain ⟨x, hx, h⟩ := bind_ok h
        cases pure_ok h
        simp only [decArmLax, heq, if_true, decS_refines t I _ _ x hx]
      · rename_i heq
        obtain ⟨y, hy, h⟩ := bind_ok h
        cases pure_ok h
        simp only [decArmLax, heq, if_false, decArmS_refines m u cs I s tag y hy]
  | n, t, .last m u => by
      intro I s tag v h
      simp only [decArmS] at h
      split at h
      · rename_i heq
        obtain ⟨x, hx, h⟩ := bind_ok h
        cases pure_ok h
        simp only [decArmLax, heq, if_true, decS_refines t I _ _ x hx]
      · rename_i heq
        split at h
        · obtain ⟨y, hy, h⟩ := bind_ok h
          cases pure_ok h
          simp only [decArmLax, heq, if_false, decS_refines u I _ _ y hy]
        · exact (throw_ok h).elim
  termination_by _ t cs => (sizeOf t + sizeOf cs, 0)
  decreasing_by all_goals simp_wf; all_goals first | omega | (have := Ctors.sizeOf_pos ‹Ctors›; omega)

end

/-- **Refinement.** Where the strict decoder succeeds, the lenient one returns
    the same value: `decStrict` is `decLax` with checks added. -/
theorem decStrict_refines {t : Ty} {I : Input} {v : Value t} (h : decStrict t I = .ok v) :
    decLax t I 0 0 = v := by
  simp only [decStrict] at h
  split at h
  · exact (throw_ok h).elim
  · exact decS_refines t I 0 0 v h

/-- On canonical input the three decoders agree: the word-level `decode` on
    `encode`, and both byte-level decoders on `encodeBytes`. -/
theorem decoders_agree (t : Ty) (v : Value t) (hfit : Fits t v)
    (hlen : 32 * (encode t v).length < 2 ^ 256) :
    decode t (encode t v) = v ∧
    decStrict t (Input.ofWire (encodeBytes t v)) = .ok v ∧
    decLax t (Input.ofWire (encodeBytes t v)) 0 0 = v :=
  have hs := decStrict_encodeBytes t v hfit hlen
  ⟨decode_encode_fits t v hfit (by omega), hs, decStrict_refines hs⟩

end AbiModel
