import AbiModel.Gen

namespace AbiModel

def okVal : Except Err Val → Bool
  | .ok _ => true
  | .error _ => false

def failedWith (e : Err) : Except Err Val → Bool
  | .error e' => e == e'
  | .ok _ => false

def rtOk (t : Ty) (v : Val) : Bool :=
  match encode t v with
  | .error _ => false
  | .ok bs =>
    match decode t bs with
    | .error _ => false
    | .ok w => w == v

def wireOf (t : Ty) (v : Val) : List UInt8 :=
  match encode t v with
  | .error _ => []
  | .ok bs => bs

def propWellTyped (s : Sample) : Bool :=
  wellTyped (Sample.ty s) (Sample.val s)

def propRoundTrip (s : Sample) : Bool :=
  rtOk (Sample.ty s) (Sample.val s)

def propEncodeStable (s : Sample) : Bool :=
  let t := Sample.ty s
  let v := Sample.val s
  match encode t v with
  | .error _ => false
  | .ok bs =>
    match decode t bs with
    | .error _ => false
    | .ok w =>
      match encode t w with
      | .error _ => false
      | .ok bs' => bs' == bs

def propWireShape (s : Sample) : Bool :=
  let t := Sample.ty s
  match encode t (Sample.val s) with
  | .error _ => false
  | .ok bs =>
    let size := List.length bs
    let aligned := size % 32 == 0
    aligned && decide (Ty.headSize t ≤ size)

mutual

def innerFits : Ty → Bool
  | .arr t => innerFits t
  | .pair a b => innerFits a && innerFits b
  | .tup t => innerFits t
  | .adt ts =>
    let fitsHere := if Ty.allStatic ts then decide (Ty.innerHead ts ≤ Ty.chainHead ts) else true
    fitsHere && innerFitsAll ts
  | _ => true

def innerFitsAll : List Ty → Bool
  | [] => true
  | t :: ts => innerFits t && innerFitsAll ts

end

def propInnerFits (s : Sample) : Bool :=
  innerFits (Sample.ty s)

def propTagsDistinct (i j : Nat) : Bool :=
  let a := i % 32
  let b := j % 32
  a == b || variantTag a != variantTag b

def propTagLenient (n : Nat) : Bool :=
  let t : Ty := .adt [.word, .word]
  let v : Val := .variant 0 (.word 5)
  let tag := wordOfNat (n + 2)
  let mutated := setWordAt (wireOf t v) 0 tag
  let fallback : Val := .variant 1 (.word 5)
  if tag == variantTag 0 then true
  else
    match decode t mutated with
    | .error _ => false
    | .ok w => w == fallback

def propPadIgnored (n : Nat) : Bool :=
  let t : Ty := .adt [.word, .pair .word .word]
  let v : Val := .variant 0 (.word 7)
  let bs := wireOf t v
  let mutated := setWordAt bs 64 (wordOfNat (n + 1))
  let sized := List.length bs == 96
  sized &&
    (match decode t mutated with
     | .error _ => false
     | .ok w => w == v)

def propTrailingIgnored (s : Sample) (n : Nat) : Bool :=
  let t := Sample.ty s
  let v := Sample.val s
  let extended := wireOf t v ++ wordToBytes (wordOfNat n)
  match decode t extended with
  | .error _ => false
  | .ok w => w == v

def propTruncationZeros (s : Sample) : Bool :=
  let t := Sample.ty s
  let bs := wireOf t (Sample.val s)
  let truncated := List.take (List.length bs - 32) bs
  okVal (decode t truncated)

def propDirtyB4 (n : Nat) : Bool :=
  let t : Ty := .b4
  let highBit := wordOfNat 1 <<< 200
  let clean := wordOfNat (n % 4294967296)
  let dirty := clean ||| highBit
  let mutated := setWordAt (wireOf t (.word clean)) 0 dirty
  let unchecked := wellTyped t (.word dirty) == false
  unchecked &&
    (match decode t mutated with
     | .error _ => false
     | .ok w => w == Val.word dirty)

def propDirtyBoolRejected (n : Nat) : Bool :=
  let dirty := wordOfNat (n % 1000 + 2)
  let mutated := setWordAt (wireOf .bool (.word 0)) 0 dirty
  failedWith .dirtyBool (decode .bool mutated)

def propDirtyAddrRejected (n : Nat) : Bool :=
  let highBit := wordOfNat 1 <<< 200
  let dirty := highBit ||| wordOfNat n
  let mutated := setWordAt (wireOf .addr (.word 0)) 0 dirty
  failedWith .dirtyAddr (decode .addr mutated)

def aliasWire (payload : List UInt8) : List UInt8 :=
  let offset := wordToBytes (wordOfNat 64)
  let len := wordToBytes (wordOfNat (List.length payload))
  offset ++ offset ++ len ++ payload

def propAliasing (bs : List UInt8) : Bool :=
  let payload := List.take 32 bs
  match decode (.pair .bytes .bytes) (aliasWire payload) with
  | .ok (.pair (.bytes x) (.bytes y)) => x == payload && y == payload
  | _ => false

def propNonInjective (bs : List UInt8) : Bool :=
  let t : Ty := .pair .bytes .bytes
  let wire := aliasWire (List.take 32 bs)
  match decode t wire with
  | .error _ => false
  | .ok v =>
    match encode t v with
    | .error _ => false
    | .ok bs' => bs' != wire

def propOffsetLenient (bs : List UInt8) : Bool :=
  let payload := List.take 32 bs
  let offset := wordToBytes (wordOfNat 64)
  let junk := wordToBytes (wordOfNat 57005)
  let len := wordToBytes (wordOfNat (List.length payload))
  let wire := offset ++ junk ++ len ++ payload
  match decode .bytes wire with
  | .ok (.bytes x) => x == payload
  | _ => false

def propArrayLenient (n : Nat) : Bool :=
  let t : Ty := .arr .word
  let v : Val := .arr [.word 1, .word 2]
  let count := 2 + n % 4
  let elemAt := fun (i : Nat) => Val.word (if i == 0 then 1 else if i == 1 then 2 else 0)
  let expected : Val := .arr (List.map elemAt (List.range count))
  let mutated := setWordAt (wireOf t v) 32 (wordOfNat count)
  match decode t mutated with
  | .error _ => false
  | .ok w => w == expected

def propTupStatic (s : Sample) : Bool :=
  let t := Sample.ty s
  if Ty.isStatic t then rtOk (.tup t) (Sample.val s) else true

def propTupDynFirst (s : Sample) : Bool :=
  let inner : Ty := .tup (.pair .word .bytes)
  let innerVal : Val := .pair (.word 1) (.bytes [7, 7])
  rtOk (.pair inner (Sample.ty s)) (.pair innerVal (Sample.val s))

def propTupDynQuirk : Bool :=
  let t : Ty := .pair .word (.tup (.pair .word .bytes))
  let v : Val := .pair (.word 1) (.pair (.word 2) (.bytes [3]))
  match decode t (wireOf t v) with
  | .error _ => false
  | .ok w => w != v

end AbiModel
