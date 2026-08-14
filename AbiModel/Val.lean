import AbiModel.Ty

namespace AbiModel

inductive Val where
  | unit
  | word : Word → Val
  | bytes : List UInt8 → Val
  | arr : List Val → Val
  | pair : Val → Val → Val
  | variant : Nat → Val → Val
  deriving Inhabited

mutual

def Val.fmt : Val → String
  | .unit => "()"
  | .word w => toString (BitVec.toNat w)
  | .bytes bs => "b" ++ toString (List.length bs)
  | .arr xs => "[" ++ Val.fmtList xs ++ "]"
  | .pair a b => "(" ++ Val.fmt a ++ "," ++ Val.fmt b ++ ")"
  | .variant i a => "v" ++ toString i ++ "(" ++ Val.fmt a ++ ")"

def Val.fmtList : List Val → String
  | [] => ""
  | [x] => Val.fmt x
  | x :: xs => Val.fmt x ++ "," ++ Val.fmtList xs

end

instance : Repr Val := ⟨fun v _ => Std.Format.text (Val.fmt v)⟩

mutual

def Val.beq : Val → Val → Bool
  | .unit, .unit => true
  | .word a, .word b => a == b
  | .bytes a, .bytes b => a == b
  | .arr a, .arr b => Val.beqList a b
  | .pair a b, .pair c d => Val.beq a c && Val.beq b d
  | .variant i a, .variant j b => i == j && Val.beq a b
  | _, _ => false

def Val.beqList : List Val → List Val → Bool
  | [], [] => true
  | x :: xs, y :: ys => Val.beq x y && Val.beqList xs ys
  | _, _ => false

end

instance : BEq Val := ⟨Val.beq⟩

mutual

def wellTyped : Ty → Val → Bool
  | .unit, .unit => true
  | .word, .word _ => true
  | .b4, .word w => w >>> 32 == 0
  | .addr, .word w => w >>> 160 == 0
  | .bool, .word w => decide (BitVec.toNat w ≤ 1)
  | .bytes, .bytes _ => true
  | .arr t, .arr xs => wellTypedAll t xs
  | .pair a b, .pair x y => wellTyped a x && wellTyped b y
  | .tup t, v => wellTyped t v
  | .adt ts, .variant i v => wellTypedAt ts i v
  | _, _ => false

def wellTypedAll (t : Ty) : List Val → Bool
  | [] => true
  | x :: xs => wellTyped t x && wellTypedAll t xs

def wellTypedAt : List Ty → Nat → Val → Bool
  | [], _, _ => false
  | t :: _, 0, v => wellTyped t v
  | _ :: ts, i + 1, v => wellTypedAt ts i v

end

end AbiModel
