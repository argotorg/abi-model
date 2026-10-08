import AbiModel.Word

namespace AbiModel

inductive Ty where
  | unit
  | word
  | bool
  | pair  : Ty → Ty → Ty
  | sum   : Ty → Ty → Ty
  | tup   : Ty → Ty
  | array : Ty → Ty
  deriving Repr, DecidableEq, Inhabited

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

end AbiModel
