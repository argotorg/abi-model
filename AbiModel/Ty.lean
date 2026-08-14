import AbiModel.Word

namespace AbiModel

inductive Ty where
  | unit
  | word
  | b4
  | addr
  | bool
  | bytes
  | arr : Ty → Ty
  | pair : Ty → Ty → Ty
  | tup : Ty → Ty
  | adt : List Ty → Ty
  deriving Inhabited

mutual

def Ty.fmt : Ty → String
  | .unit => "unit"
  | .word => "word"
  | .b4 => "b4"
  | .addr => "addr"
  | .bool => "bool"
  | .bytes => "bytes"
  | .arr t => "arr(" ++ Ty.fmt t ++ ")"
  | .pair a b => "(" ++ Ty.fmt a ++ "," ++ Ty.fmt b ++ ")"
  | .tup t => "tup(" ++ Ty.fmt t ++ ")"
  | .adt ts => "adt[" ++ Ty.fmtList ts ++ "]"

def Ty.fmtList : List Ty → String
  | [] => ""
  | [t] => Ty.fmt t
  | t :: ts => Ty.fmt t ++ "|" ++ Ty.fmtList ts

end

instance : Repr Ty := ⟨fun t _ => Std.Format.text (Ty.fmt t)⟩

mutual

def Ty.isStatic : Ty → Bool
  | .unit => true
  | .word => true
  | .b4 => true
  | .addr => true
  | .bool => true
  | .bytes => false
  | .arr _ => false
  | .pair a b => Ty.isStatic a && Ty.isStatic b
  | .tup t => Ty.isStatic t
  | .adt ts => Ty.allStatic ts

def Ty.allStatic : List Ty → Bool
  | [] => true
  | t :: ts => Ty.isStatic t && Ty.allStatic ts

end

mutual

def Ty.headSize : Ty → Nat
  | .unit => 0
  | .word => 32
  | .b4 => 32
  | .addr => 32
  | .bool => 32
  | .bytes => 32
  | .arr _ => 32
  | .pair a b => Ty.headSize a + Ty.headSize b
  | .tup t => if Ty.isStatic t then Ty.headSize t else 32
  | .adt ts => Ty.chainHead ts

def Ty.chainHead : List Ty → Nat
  | [] => 0
  | [t] => Ty.headSize t
  | t :: ts =>
    let allStatic := Ty.isStatic t && Ty.allStatic ts
    if allStatic then 32 + max (Ty.headSize t) (Ty.chainHead ts) else 32

def Ty.maxHead : List Ty → Nat
  | [] => 0
  | t :: ts => max (Ty.headSize t) (Ty.maxHead ts)

end

def Ty.innerHead (ts : List Ty) : Nat := 32 + Ty.maxHead ts

def variantTag (i : Nat) : Word :=
  wordOfNat (0x9e3779b97f4a7c15 * (i + 1) + 0xbf58476d1ce4e5b9)

def Ty.nth : List Ty → Nat → Option Ty
  | [], _ => none
  | t :: _, 0 => some t
  | _ :: ts, i + 1 => Ty.nth ts i

end AbiModel
