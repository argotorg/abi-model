import AbiModel.Ty

namespace AbiModel

def Value : Ty → Type
  | .unit => Unit
  | .word => Word
  | .bool => Bool
  | .pair a b => Value a × Value b
  | .sum a b => Value a ⊕ Value b
  | .tup a => Value a
  | .array a => List (Value a)

end AbiModel
