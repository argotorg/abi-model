import AbiModel.Encode

namespace AbiModel

def decode : (t : Ty) → Wire → Option (Value t × Wire)
  | .unit, w => some ((), w)
  | .word, [] => none
  | .word, x :: rest => some (x, rest)
  | .bool, [] => none
  | .bool, x :: rest => some (x != 0, rest)
  | .pair a b, w =>
    match decode a w with
    | none => none
    | some (x, w1) =>
      match decode b w1 with
      | none => none
      | some (y, w2) => some ((x, y), w2)
  | .sum _ _, [] => none
  | .sum a b, tag :: rest =>
    if tag = 0 then
      match decode a rest with
      | none => none
      | some (x, w1) => some (Sum.inl x, w1.drop (padL a b))
    else
      match decode b rest with
      | none => none
      | some (y, w1) => some (Sum.inr y, w1.drop (padR a b))
  | .tup a, w => decode a w

def decodeAll (t : Ty) (w : Wire) : Option (Value t) :=
  match decode t w with
  | some (v, _) => some v
  | none => none

end AbiModel
