import AbiModel.Word

namespace AbiModel

mutual

inductive Ty where
  | unit
  | word
  | bool
  | pair  : Ty → Ty → Ty
  | sum   : Ty → Ty → Ty
  | tup   : Ty → Ty
  | array : Ty → Ty
  /-- A derived multi-constructor enum: a first constructor `name(payload)` and the
      remaining (at least one) constructors. Each payload is the constructor's
      `constrRep` (`DeriveGeneric.hs`): `unit` for no fields, the field's type
      for one field, a right-nested `pair` for several. Unlike the primitive
      `sum`, an enum carries a single `keccak256("Name(argSigs)")` tag word. -/
  | enum  : String → Ty → Ctors → Ty

/-- The constructors of an enum after the first, in declaration order. -/
inductive Ctors where
  | last : String → Ty → Ctors
  | cons : String → Ty → Ctors → Ctors

end

deriving instance Repr for Ty, Ctors
deriving instance DecidableEq for Ty, Ctors

instance : Inhabited Ty := ⟨.unit⟩

/-- Used by the termination proofs of the per-constructor (`arm*`) helpers. -/
theorem Ctors.sizeOf_pos (cs : Ctors) : 0 < sizeOf cs := by
  cases cs <;> simp only [Ctors.last.sizeOf_spec, Ctors.cons.sizeOf_spec] <;> omega

/-!
An enum `enum n₀ t₀ (cons n₁ t₁ (last n₂ t₂))` has the SOP rep
`sum<t₀, sum<t₁, t₂>>`; its staticness is that of the rep. Its head width is
not: the derived `ABIAttribs` instance (solcore-rs `derived_abi.rs`) reserves a
single tag word and the widest payload, `1 + max(h₀, h₁, h₂)`, where the rep
would reserve one tag word per nesting level, `1 + max(h₀, 1 + max(h₁, h₂))`.
-/
mutual

/-- A type is *static* when its size does not depend on the value: no dynamic
    array appears in it. Dynamic types occupy a single offset word in the head. -/
def isStatic : Ty → Bool
  | .unit => true
  | .word => true
  | .bool => true
  | .pair a b => isStatic a && isStatic b
  | .sum a b => isStatic a && isStatic b
  | .tup a => isStatic a
  | .array _ => false
  | .enum _ t cs => isStatic t && isStaticC cs

/-- Staticness of the rep of the remaining constructors. -/
def isStaticC : Ctors → Bool
  | .last _ t => isStatic t
  | .cons _ t cs => isStatic t && isStaticC cs

end

mutual

/-- Width of a type's *head* region, in 256-bit words (the std uses bytes = 32×).
    A dynamic node contributes a single offset word. -/
def headWords : Ty → Nat
  | .unit => 0
  | .word => 1
  | .bool => 1
  | .pair a b => headWords a + headWords b
  | .sum a b => if isStatic a && isStatic b then 1 + max (headWords a) (headWords b) else 1
  | .tup a => if isStatic a then headWords a else 1
  | .array _ => 1
  -- one tag word and the widest payload head (flat, unlike the nested `sum`)
  | .enum _ t cs => if isStatic t && isStaticC cs then 1 + max (headWords t) (maxArmC cs) else 1

/-- Widest constructor payload head of the remaining constructors. -/
def maxArmC : Ctors → Nat
  | .last _ t => headWords t
  | .cons _ t cs => max (headWords t) (maxArmC cs)

end

end AbiModel
