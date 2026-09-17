import AbiModel.Val

namespace AbiModel

/--
    The number of padding words a static sum a b
    adds after an inl branch of width headWords a,
    so both branches fill the same max(...)-wide union.
-/
def padL (a b : Ty) : Nat := max (headWords a) (headWords b) - headWords a

/--
    The padding after an inr branch of width headWords b.
-/
def padR (a b : Ty) : Nat := max (headWords a) (headWords b) - headWords b

mutual

-- the encode head/tail function : TODO: make the threading of the head and tail explicit and consistent
  def encode_ht (t : Ty) (v : Value t) (headSize : Nat) (head tail : Wire) : Wire × Wire :=
    match t, v with
    | .unit, _ => (head, tail)
    | .word, w => (head ++ ([w] : Wire) , tail)
    | .bool, b => (head ++ [bif b then 1 else 0], tail)
    | .pair a b, (x, y) => let (enc_a_head, enc_a_tail) := encode_ht a x headSize head tail
                           encode_ht b y headSize enc_a_head enc_a_tail
    | .sum a b, Sum.inl x => let (enc_head, enc_tail) := encode_ht a x headSize head tail
                             (0 :: enc_head ++ (List.replicate (padL a b) 0), enc_tail)
    | .sum a b, Sum.inr y => let (enc_head, enc_tail) := encode_ht b y headSize head tail
                             (1 :: enc_head ++ List.replicate (padR a b) 0, enc_tail)
    | .tup a, x => encode_ht a x headSize head tail
    | .arr a, vals => encodeArr a vals headSize [] []
  termination_by (sizeOf t, 1)

  def encodeArr (a : Ty) (vals : List (Value a)) (headSize : Nat) (head tail: Wire) : Wire × Wire :=
      match vals with
      | [] => (head, tail)
      | value :: rest =>
          let (enc_head, enc_tail) := encode_ht a value (headSize + tail.length) [] []
          let encoded := enc_head ++ enc_tail
          let offset := [BitVec.ofNat 256 (headSize + tail.length)]
          encodeArr a rest (headSize) (head ++ offset) (tail ++ encoded)
    termination_by (sizeOf a, vals.length + 1)

end

/--
     Canonical ABI encoder (head/tail, static fragment).
     Aligned with ABIEncode.encodeInto

    * atoms write one head word (bool as 0/1),
    * a pair concatenates its components,
    * a static sum writes the tag word (0 = inl, 1 = inr)
      followed by the selected branch, padded to the
      widest branch.
-/
def encode (t : Ty) (v : Value t) : Wire :=
  let headSize := headWords t
  let (head, tail) := encode_ht t v headSize [] []
  head ++ tail

end AbiModel
