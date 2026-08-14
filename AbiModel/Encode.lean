import AbiModel.Val

namespace AbiModel

inductive Err where
  | dirtyBool
  | dirtyAddr
  | outOfBounds
  | typeMismatch
  | limit
  deriving Repr, BEq, Inhabited

def gasBudget : Nat := 64

mutual

def encInto (gas : Nat) (t : Ty) (v : Val) (m : Mem) (basePtr offset tail : Word) :
    Except Err (Mem × Word) :=
  match gas with
  | 0 => .error .limit
  | g + 1 =>
    let headSlot := basePtr + offset
    let relTail := tail - basePtr
    match t, v with
    | .unit, _ => .ok (m, tail)
    | .word, .word w => .ok (Mem.storeWord m headSlot w, tail)
    | .b4, .word w => .ok (Mem.storeWord m headSlot w, tail)
    | .addr, .word w => .ok (Mem.storeWord m headSlot w, tail)
    | .bool, .word w => .ok (Mem.storeWord m headSlot w, tail)
    | .bytes, .bytes bs =>
      let len := List.length bs
      let padded := roundUp32 len
      let dataStart := tail + 32
      let m := Mem.storeWord m headSlot relTail
      let m := Mem.storeWord m tail (wordOfNat len)
      let m := Mem.storeBytes m dataStart bs
      let m := Mem.grow m (BitVec.toNat dataStart + padded)
      .ok (m, dataStart + wordOfNat padded)
    | .arr te, .arr xs =>
      let count := List.length xs
      let elemHead := Ty.headSize te
      let region := tail + 32
      let innerTail := region + wordOfNat (count * elemHead)
      let m := Mem.storeWord m headSlot relTail
      let m := Mem.storeWord m tail (wordOfNat count)
      encSeq g te xs m region 0 (wordOfNat elemHead) innerTail
    | .pair a b, .pair x y =>
      match encInto g a x m basePtr offset tail with
      | .error e => .error e
      | .ok (m, tail) =>
        let rightOffset := offset + wordOfNat (Ty.headSize a)
        encInto g b y m basePtr rightOffset tail
    | .tup te, _ =>
      if Ty.isStatic te then encInto g te v m basePtr offset tail
      else
        let bodyTail := tail + wordOfNat (Ty.headSize te)
        let m := Mem.storeWord m basePtr relTail
        encInto g te v m tail 0 bodyTail
    | .adt ts, .variant i x =>
      match Ty.nth ts i with
      | none => .error .outOfBounds
      | some te =>
        let tag := variantTag i
        if Ty.allStatic ts then
          let m := Mem.storeWord m headSlot tag
          encInto g te x m basePtr (offset + 32) tail
        else
          let bodyTail := tail + wordOfNat (Ty.innerHead ts)
          let m := Mem.storeWord m headSlot relTail
          let m := Mem.storeWord m tail tag
          encInto g te x m tail 32 bodyTail
    | _, _ => .error .typeMismatch
termination_by (gas, 0)

def encSeq (gas : Nat) (te : Ty) (xs : List Val) (m : Mem) (base off hs tail : Word) :
    Except Err (Mem × Word) :=
  match xs with
  | [] => .ok (m, tail)
  | x :: rest =>
    match encInto gas te x m base off tail with
    | .error e => .error e
    | .ok (m, tail) => encSeq gas te rest m base (off + hs) hs tail
termination_by (gas, List.length xs + 1)

end

def encode (t : Ty) (v : Val) : Except Err (List UInt8) :=
  let initTail := wordOfNat (Ty.headSize t)
  let empty := Array.emptyWithCapacity 0
  match encInto gasBudget t v empty 0 0 initTail with
  | .error e => .error e
  | .ok (m, tail) => .ok (Mem.loadBytes m 0 (BitVec.toNat tail))

end AbiModel
