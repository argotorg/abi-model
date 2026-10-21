import Plausible
import AbiDiff.Solc

/-!
Random cases for the differential test.

Generation is type-directed: a `Ty` is drawn from the grammar of types the std
can `abi_encode` (`supported`), then a `Value` of that type, so the Solcore source
rendered from it is well typed by construction. Shrinking goes through Plausible's
`Shrinkable`; the test loop itself is driven from `IO` because the oracle
(compiling and running a contract) is external and works in batches.
-/

namespace AbiDiff
open AbiModel Plausible

/-- Types of depth at most `n`, all `supported`. Without `tup`, no `ABITuple`
    occurs (enum payloads, see `solTy`). -/
def genTy (n : Nat) (tup : Bool := true) : Gen Ty :=
  match n with
  | 0 => Gen.frequency (pure .word)
      [(4, pure .word), (1, pure .bool), (1, pure .unit), (2, pure (.array .word))]
  | n + 1 => Gen.frequency (pure .word) ([
      (3, pure .word), (1, pure .bool), (1, pure .unit), (2, pure (.array .word)),
      (3, do return .pair (← genTy n tup) (← genTy n tup)),
      (2, do return .sum (← genTy n tup) (← genTy n tup)),
      -- two or three constructors, named by position so their tags are distinct
      (2, do
        let t₀ ← genTy n false
        let t₁ ← genTy n false
        if (← Gen.elements [true, false] (by decide)) then return .enum "A" t₀ (.last "B" t₁)
        else return .enum "A" t₀ (.cons "B" t₁ (.last "C" (← genTy n false))))] ++
      if tup then [(1, do return .tup (← genTy n))] else [])

def boundaryWords : List Word := [0, 1, 2, 2 ^ 255, 2 ^ 256 - 1, 2 ^ 256 - 2]

def genWord : Gen Word := Gen.frequency (pure 0) [
  (3, do return natW (← Gen.choose Nat 0 16 (by decide)).val),
  (2, Gen.elements boundaryWords (by decide)),
  (1, do return natW (← Gen.choose Nat 0 (2 ^ 256 - 1) (Nat.zero_le _)).val)]

/-- Number of constructors in `cs`. -/
def ctorCount : Ctors → Nat
  | .last .. => 1
  | .cons _ _ cs => 1 + ctorCount cs

mutual

def genVal : (t : Ty) → Gen (Value t)
  | .unit => pure ()
  | .word => genWord
  | .bool => Gen.elements [true, false] (by decide)
  | .pair a b => do return (← genVal a, ← genVal b)
  | .sum a b => do
      if (← Gen.elements [true, false] (by decide)) then return .inl (← genVal a)
      else return .inr (← genVal b)
  | .tup a => genVal a
  | .array a => do
      let n := (← Gen.choose Nat 0 4 (by decide)).val
      (List.range n).mapM fun _ => genVal a
  | .enum _ t cs => genArm t cs
  termination_by t => (sizeOf t, 2)

/-- A value of an enum: each constructor is equally likely. -/
def genArm (t : Ty) (cs : Ctors) : Gen (Value t ⊕ ValueC cs) := do
  if (← Gen.choose Nat 0 (ctorCount cs) (Nat.zero_le _)).val == 0 then return .inl (← genVal t)
  else return .inr (← genArmC cs)
  termination_by (sizeOf t + sizeOf cs, 1)
  decreasing_by all_goals simp_wf; all_goals first | omega | (have := Ctors.sizeOf_pos ‹Ctors›; omega)

def genArmC : (cs : Ctors) → Gen (ValueC cs)
  | .last _ u => genVal u
  | .cons _ u cs => genArm u cs
  termination_by cs => (sizeOf cs, 0)

end

def genCase (depth : Nat) : Gen Case := do
  let t ← genTy depth
  return ⟨t, ← genVal t⟩

/-- `n` cases from `seed`; the same seed always gives the same cases. -/
def sampleCases (seed n depth : Nat) : Except String (List Case) :=
  match ReaderT.run (runRandWith seed ((List.range n).mapM fun _ => genCase depth)) ⟨depth⟩ with
  | .ok cs => .ok cs
  | .error (.genError e) => .error e

/-! ## Shrinking -/

def dropOne : List α → List (List α)
  | [] => []
  | x :: xs => xs :: (dropOne xs).map (x :: ·)

def shrinkEach (f : α → List α) : List α → List (List α)
  | [] => []
  | x :: xs => (f x).map (· :: xs) ++ (shrinkEach f xs).map (x :: ·)

def shrinkWord (w : Word) : List Word :=
  ([0, 1, w / 2, w - 1].filter (·.toNat < w.toNat)).eraseDups

mutual

/-- Smaller values of the same type. -/
def shrinkVal : (t : Ty) → Value t → List (Value t)
  | .unit, _ => []
  | .word, w => shrinkWord w
  | .bool, b => if b then [false] else []
  | .pair a b, v => (shrinkVal a v.1).map (·, v.2) ++ (shrinkVal b v.2).map (v.1, ·)
  | .sum a _, .inl x => (shrinkVal a x).map .inl
  | .sum _ b, .inr y => (shrinkVal b y).map .inr
  | .tup a, x => shrinkVal a x
  | .array a, xs => dropOne xs ++ shrinkEach (shrinkVal a) xs
  | .enum _ t cs, v => shrinkArm t cs v
  termination_by t => (sizeOf t, 2)

/-- Smaller payloads of the selected constructor (the constructor is kept). -/
def shrinkArm : (t : Ty) → (cs : Ctors) → Value t ⊕ ValueC cs → List (Value t ⊕ ValueC cs)
  | t, _, .inl x => (shrinkVal t x).map .inl
  | _, cs, .inr y => (shrinkArmC cs y).map .inr
  termination_by t cs => (sizeOf t + sizeOf cs, 1)
  decreasing_by all_goals simp_wf; all_goals first | omega | (have := Ctors.sizeOf_pos ‹Ctors›; omega)

def shrinkArmC : (cs : Ctors) → ValueC cs → List (ValueC cs)
  | .last _ u, y => shrinkVal u y
  | .cons _ u cs, y => shrinkArm u cs y
  termination_by cs => (sizeOf cs, 0)

end

mutual

/-- The selected constructor's payload of an enum, as a case of its own. -/
def armCase : (t : Ty) → (cs : Ctors) → Value t ⊕ ValueC cs → Case
  | t, _, .inl x => ⟨t, x⟩
  | _, cs, .inr y => armCaseC cs y
  termination_by _ cs => (sizeOf cs, 1)

def armCaseC : (cs : Ctors) → ValueC cs → Case
  | .last _ u, y => ⟨u, y⟩
  | .cons _ u cs, y => armCase u cs y
  termination_by cs => (sizeOf cs, 0)

end

/-- Cases of a smaller type, keeping the part of the value that lives there. -/
def shrinkTy (c : Case) : List Case :=
  match c with
  | ⟨.pair a b, v⟩ => [⟨a, v.1⟩, ⟨b, v.2⟩]
  | ⟨.sum a _, .inl x⟩ => [⟨a, x⟩]
  | ⟨.sum _ b, .inr y⟩ => [⟨b, y⟩]
  | ⟨.tup a, x⟩ => [⟨a, x⟩]
  | ⟨.enum _ t cs, v⟩ => [armCase t cs v]
  | _ => []

/-- Type shrinks first (they cut the most), then value shrinks. -/
instance : Shrinkable Case where
  shrink c := (shrinkTy c ++ (shrinkVal c.t c.v).map (fun v => (⟨c.t, v⟩ : Case))).filter
    (supported ·.t)

end AbiDiff

namespace AbiDiff

-- generated types are always in the supported fragment, and generation is
-- deterministic in the seed
#guard match sampleCases 7 200 3 with
  | .ok cs => cs.all (supported ·.t) && cs.length == 200
  | .error _ => false
#guard match sampleCases 7 20 3, sampleCases 7 20 3 with
  | .ok a, .ok b => a.map Case.describe == b.map Case.describe
  | _, _ => false

end AbiDiff
