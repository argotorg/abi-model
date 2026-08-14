import AbiModel.Encode

namespace AbiModel

def byteLimit : Nat := 4096

def elemLimit : Nat := 64

mutual

def decAt (gas : Nat) (t : Ty) (m : Mem) (base headOffset : Word) : Except Err Val :=
  match gas with
  | 0 => .error .limit
  | g + 1 =>
    let headSlot := base + headOffset
    match t with
    | .unit => .ok .unit
    | .word => .ok (.word (Mem.loadWord m headSlot))
    | .b4 => .ok (.word (Mem.loadWord m headSlot))
    | .addr =>
      let w := Mem.loadWord m headSlot
      if w >>> 160 == 0 then .ok (.word w) else .error .dirtyAddr
    | .bool =>
      let w := Mem.loadWord m headSlot
      if BitVec.toNat w ≤ 1 then .ok (.word w) else .error .dirtyBool
    | .bytes =>
      let bodyStart := base + Mem.loadWord m headSlot
      let len := BitVec.toNat (Mem.loadWord m bodyStart)
      if len > byteLimit then .error .limit
      else .ok (.bytes (Mem.loadBytes m (bodyStart + 32) len))
    | .arr te =>
      let handle := base + Mem.loadWord m headSlot
      let count := BitVec.toNat (Mem.loadWord m handle)
      if count > elemLimit then .error .limit
      else
        let region := handle + 32
        let step := wordOfNat (Ty.headSize te)
        match decSeq g te m region step count 0 with
        | .error e => .error e
        | .ok xs => .ok (.arr xs)
    | .pair a b =>
      match decAt g a m base headOffset with
      | .error e => .error e
      | .ok x =>
        let rightOffset := headOffset + wordOfNat (Ty.headSize a)
        match decAt g b m base rightOffset with
        | .error e => .error e
        | .ok y => .ok (.pair x y)
    | .tup te =>
      let bodyBase := if Ty.isStatic te then headSlot else base + Mem.loadWord m base
      decAt g te m bodyBase 0
    | .adt ts =>
      let sumStart := if Ty.allStatic ts then headOffset else Mem.loadWord m headSlot
      decPick g ts 0 m (base + sumStart)
termination_by (gas, 0)

def decSeq (gas : Nat) (te : Ty) (m : Mem) (base step : Word) (n i : Nat) :
    Except Err (List Val) :=
  match n with
  | 0 => .ok []
  | k + 1 =>
    let elemOffset := step * wordOfNat i
    match decAt gas te m base elemOffset with
    | .error e => .error e
    | .ok x =>
      match decSeq gas te m base step k (i + 1) with
      | .error e => .error e
      | .ok xs => .ok (x :: xs)
termination_by (gas, n + 1)

def decPick (gas : Nat) (ts : List Ty) (i : Nat) (m : Mem) (base : Word) : Except Err Val :=
  match ts with
  | [] => .error .outOfBounds
  | [te] =>
    match decAt gas te m base 32 with
    | .error e => .error e
    | .ok v => .ok (.variant i v)
  | te :: rest =>
    let tag := Mem.loadWord m base
    if tag == variantTag i then
      match decAt gas te m base 32 with
      | .error e => .error e
      | .ok v => .ok (.variant i v)
    else decPick gas rest (i + 1) m base
termination_by (gas, List.length ts + 1)

end

def decode (t : Ty) (bs : List UInt8) : Except Err Val :=
  decAt gasBudget t (List.toArray bs) 0 0

end AbiModel
