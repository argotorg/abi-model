import AbiModel.Ty

namespace AbiModel

mutual

@[reducible] def Value : Ty → Type
  | .unit => Unit
  | .word => Word
  | .bool => Bool
  | .pair a b => Value a × Value b
  | .sum a b => Value a ⊕ Value b
  | .tup a => Value a
  | .array a => List (Value a)
  | .enum _ t cs => Value t ⊕ ValueC cs

/-- A value of one of the remaining constructors, as in the SOP rep
    (`inl` = this constructor, `inr` = a later one). -/
@[reducible] def ValueC : Ctors → Type
  | .last _ t => Value t
  | .cons _ t cs => Value t ⊕ ValueC cs

end

end AbiModel
