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
    | .sum a b, Sum.inl x => let (enc_head, enc_tail) := encode_ht a x headSize [] tail
                             (head ++ [0] ++ enc_head ++ (List.replicate (padL a b) 0), enc_tail)
    | .sum a b, Sum.inr y => let (enc_head, enc_tail) := encode_ht b y headSize [] tail
                             (head ++ [1] ++ enc_head ++ List.replicate (padR a b) 0, enc_tail)
    | .tup a, x => encode_ht a x headSize head tail
    | .arr a, vals => let offset := [BitVec.ofNat 256 (headSize + tail.length + 1)]
                      let l :=  [BitVec.ofNat 256 (List.length vals)]
                      encodeArr a vals headSize (head ++ offset) (tail ++ l)
  termination_by (sizeOf t, 1)

-- [(7, Sum.inr 0)] --> [2,1,7,1,0] instead of [2,1,1,7,0]
  def encodeArr (a : Ty) (vals : List (Value a)) (headSize : Nat) (head tail: Wire) : Wire × Wire :=
      match vals with
      | [] => (head, tail)
      | value :: rest =>
          let (enc_head, enc_tail) := encode_ht a value (headSize + tail.length + 1) [] []
          let encoded := enc_head ++ enc_tail
          encodeArr a rest (headSize) head (tail ++ encoded)
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

def test_array_ty : Ty := Ty.arr (Ty.arr Ty.word)

def test_array_val : Value test_array_ty := [[0, 1], [2, 3, 4]]

#eval encode test_array_ty test_array_val

def test1_array_ty : Ty := Ty.arr (Ty.pair Ty.word (Ty.sum Ty.word Ty.word))
def test1_array_val : Value test1_array_ty := [(5, Sum.inl 6), (8, Sum.inr 9), (7, Sum.inr 0)]

#eval encode test1_array_ty test1_array_val

def test2_array_ty : Ty := Ty.arr ((Ty.sum Ty.word Ty.word))
def test2_array_val : Value test2_array_ty := [Sum.inl 0, Sum.inr 2, Sum.inl 3]

#eval encode test2_array_ty test2_array_val

def test3_array_ty : Ty := Ty.arr (Ty.pair Ty.word Ty.word)
def test3_array_val : Value test3_array_ty := [(0, 4), (1, 5), (2, 6)]

#eval encode test3_array_ty test3_array_val

def test4_array_ty : Ty := Ty.pair Ty.word (Ty.sum Ty.word Ty.word)
def test4_array_val : Value test4_array_ty := (7, Sum.inl 4)

#eval encode test4_array_ty test4_array_val

def test5_array_ty : Ty := Ty.sum Ty.word (Ty.pair Ty.word Ty.word)
def test5_array_val : Value test5_array_ty := Sum.inr (7, 4)

#eval encode test5_array_ty test5_array_val



end AbiModel
