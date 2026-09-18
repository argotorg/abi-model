import AbiModel.Encode

namespace AbiModel


mutual

def decodeHeadTail (t : Ty) (headSize : Nat) (head tail : Wire) (tailCursor: Nat): Option (Value t × Wire × Wire) :=
  match t, head with
  | .unit, _ => some ((() , head, tail))
  | .word, x :: rest => some (x, rest, tail)
  | .word, [] => none
  | .bool, x :: rest => some (x != 0, rest, tail)
  | .bool, [] => none
  | .pair a b, w =>
    match decodeHeadTail a headSize w tail tailCursor with
    | none => none
    | some (x, head', tail') =>
      match decodeHeadTail b headSize head' tail' tailCursor with
      | none => none
      | some (y, head'', tail'') => some ((x, y), head'', tail'')
  | .sum _ _, [] => none
  | .sum a b, tag :: rest =>
    if tag = 0 then
      match decodeHeadTail a headSize rest tail tailCursor with
      | none => none
      | some (x, head', tail') => some (Sum.inl x, head'.drop (padL a b), tail')
    else
      match decodeHeadTail b headSize rest tail tailCursor with
      | none => none
      | some (y, head', tail') => some (Sum.inr y, head'.drop (padR a b), tail')
  | .tup a, w => decodeHeadTail a headSize head tail tailCursor
  | .arr a, w => decodeArr a head tail headSize tailCursor


def decodeArr (a : Ty) (head tail : Wire) (headSize : Nat) (tailCursor: Nat): Option (List (Value a) × Wire × Wire) :=
  match head with
  | [] => none
  | x :: xs =>
    if x != headSize + tailCursor then
      none
    else
      let v = decodeHeadTail a headSize xs tail (tailCursor + 1)

def decodeArrElems (a : Ty)  (n : Nat) (tail : Wire) (values : List (Value a)) (tailCursor : Nat) : Option (List (Value a) × Wire × Nat) :=
  match n with
  | 0 => some (values, tail, tailCursor)
  | n' + 1 =>
    let
    match decodeHeadTail a 0 tail tailCursor with
    | none => none
    | some (v, head', tail') => decodeArrElems a tail' (values ++ [v]) (tailCursor + 1)



end

def decode (t : Ty) (w : Wire) : Option (Value t):=
  let headsize := headWords t
  let (head, tail) := w.splitAt headsize
  match decodeHeadTail t headsize head tail 0 with
  | some (v, [], []) => some (v)
  | some (_ , _ , _) => none
  | none => none


-- def decodeAll (t : Ty) (w : Wire) : Option (Value t) :=
--   match decode t w with
--   | some (v, _) => some v
--   | none => none


end AbiModel
