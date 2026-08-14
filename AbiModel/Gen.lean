import AbiModel.Decode
import Plausible

namespace AbiModel

open Plausible

def genTy : Nat → Gen Ty
  | 0 => Gen.elements [Ty.unit, Ty.word, Ty.b4, Ty.addr, Ty.bool, Ty.bytes] (by decide)
  | n + 1 =>
    let genTup : Gen Ty := do
      let t ← genTy n
      return if Ty.isStatic t then Ty.tup t else t
    let genAdt : Gen Ty := do
      let a ← genTy n
      let b ← genTy n
      let wide ← Gen.chooseAny Bool
      if wide then
        let c ← genTy n
        return Ty.adt [a, b, c]
      else
        return Ty.adt [a, b]
    Gen.frequency (pure Ty.word)
      [(1, pure Ty.unit),
       (2, pure Ty.word),
       (2, pure Ty.b4),
       (2, pure Ty.addr),
       (2, pure Ty.bool),
       (2, pure Ty.bytes),
       (3, Ty.arr <$> genTy n),
       (4, Ty.pair <$> genTy n <*> genTy n),
       (2, genTup),
       (4, genAdt)]

instance : Arbitrary Ty where
  arbitrary := do
    let n ← Gen.getSize
    genTy (min n 3)

mutual

def zeroVal : Ty → Val
  | .unit => .unit
  | .word => .word 0
  | .b4 => .word 0
  | .addr => .word 0
  | .bool => .word 0
  | .bytes => .bytes []
  | .arr _ => .arr []
  | .pair a b => .pair (zeroVal a) (zeroVal b)
  | .tup t => zeroVal t
  | .adt ts => .variant 0 (zeroValHead ts)

def zeroValHead : List Ty → Val
  | [] => .unit
  | t :: _ => zeroVal t

end

def maskWord (bits : Nat) : Word := wordOfNat (2 ^ bits - 1)

def genVal (gas : Nat) (t : Ty) : Gen Val :=
  match gas with
  | 0 => pure (zeroVal t)
  | g + 1 =>
    let genWord : Gen Word := Arbitrary.arbitrary
    let genMasked := fun (bits : Nat) => (fun w => Val.word (w &&& maskWord bits)) <$> genWord
    match t with
    | .unit => pure .unit
    | .word => (fun w => Val.word w) <$> genWord
    | .b4 => genMasked 32
    | .addr => genMasked 160
    | .bool => (fun b => Val.word (if b then 1 else 0)) <$> (Arbitrary.arbitrary : Gen Bool)
    | .bytes =>
      let genBytes := Gen.listOf (Arbitrary.arbitrary : Gen UInt8)
      Val.bytes <$> Gen.resize (fun n => min n 40) genBytes
    | .arr te => Val.arr <$> Gen.resize (fun n => min n 3) (Gen.listOf (genVal g te))
    | .pair a b => do
      let x ← genVal g a
      let y ← genVal g b
      return .pair x y
    | .tup te => genVal g te
    | .adt ts => do
      let lo ← Gen.chooseAny Bool
      let hi ← Gen.chooseAny Bool
      let raw := (if lo then 1 else 0) + (if hi then 2 else 0)
      let count := List.length ts
      let i := if count == 0 then 0 else raw % count
      match Ty.nth ts i with
      | none => pure (zeroVal t)
      | some te => (fun v => Val.variant i v) <$> genVal g te

structure Sample where
  ty : Ty
  val : Val
  deriving Inhabited

instance : Repr Sample :=
  ⟨fun s _ =>
    let shown := Ty.fmt (Sample.ty s) ++ " |-> " ++ Val.fmt (Sample.val s)
    Std.Format.text shown⟩

instance : Arbitrary Sample where
  arbitrary := do
    let n ← Gen.getSize
    let t ← genTy (min n 3)
    let v ← genVal 8 t
    return ⟨t, v⟩

def shrinkVal : Val → List Val
  | .bytes bs =>
    let half := List.take (List.length bs / 2) bs
    if List.isEmpty bs then [] else [.bytes [], .bytes half]
  | .arr xs =>
    let half := List.take (List.length xs / 2) xs
    if List.isEmpty xs then [] else [.arr [], .arr half]
  | .pair a b =>
    let left := List.map (fun x => Val.pair x b) (shrinkVal a)
    let right := List.map (fun y => Val.pair a y) (shrinkVal b)
    left ++ right
  | .variant i a => List.map (fun x => Val.variant i x) (shrinkVal a)
  | _ => []

instance : Shrinkable Sample where
  shrink s :=
    let t := Sample.ty s
    List.map (fun v => ⟨t, v⟩) (shrinkVal (Sample.val s))

end AbiModel
