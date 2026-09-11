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
    match t, v with
    | .unit, _ => []
    | .word, w => [w]
    | .bool, b => [bif b then 1 else 0]
    | .pair a b, (x, y) => encode a x ++ encode b y
    | .sum a b, Sum.inl x => 0 :: (encode a x ++ List.replicate (padL a b) 0)
    | .sum a b, Sum.inr y => 1 :: (encode b y ++ List.replicate (padR a b) 0)
    | .tup a, x => encode a x
    | .arr a, vals => encodeArr a vals (headWords (.arr a)) [] []
    termination_by (sizeOf t, sizeOf v)

  def encodeArr (a : Ty) (vals : List (Value a)) (headSize : Nat) (head tail: Wire) : Wire :=
      match vals with
      | [] => head ++ tail
      | value :: rest =>
          let encoded := encode a value
          let offset := [BitVec.ofNat 256 (headSize + tail.length)]
          encodeArr a rest (headSize + 1) (head ++ offset) (tail ++ encoded)
    termination_by (sizeOf a, vals.length + 1)

end

end AbiModel
