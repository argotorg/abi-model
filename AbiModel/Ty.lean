import AbiModel.Word

namespace AbiModel

inductive Ty where
  | unit
  | word
  | bool
  | pair : Ty → Ty → Ty
  | sum  : Ty → Ty → Ty
  | tup  : Ty → Ty
  | arr : Ty → Ty
  deriving Repr, DecidableEq, Inhabited

def headWords : Ty → Nat
  | .unit => 0
  | .word => 1
  | .bool => 1
  | .pair a b => headWords a + headWords b
  | .sum a b => 1 + max (headWords a) (headWords b)
  | .tup a => headWords a
  | .arr _ => 1

end AbiModel
