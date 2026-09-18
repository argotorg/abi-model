import AbiModel.Decode

namespace AbiModel

theorem decode_encode (t : Ty) :
    ∀ (v : Value t) (rest : Wire), 
      decode t (encode t v ++ rest) = some (v, rest) := by
  induction t with
  | unit => intro v rest; cases v; simp [encode, decode]
  | word => intro v rest; grind [encode, decode]
  | bool => intro v rest; cases v <;> simp [encode, decode]
  | pair a b iha ihb =>
      intro v rest
      obtain ⟨x, y⟩ := v
      simp [encode, decode, List.append_assoc, iha, ihb]
  | sum a b iha ihb =>
      intro v rest
      cases v with
      | inl x => simp [encode, decode, List.append_assoc, iha, padL]
      | inr y => simp [encode, decode, List.append_assoc, ihb, padR]
  | tup a iha => intro v rest; apply iha

theorem decodeAll_encode (t : Ty) (v : Value t) :
    decodeAll t (encode t v) = some v := by
  have h := decode_encode t v []
  simp only [List.append_nil] at h
  simp [decodeAll, h]

end AbiModel
