namespace AbiModel

abbrev Word := BitVec 256

abbrev Mem := Array UInt8

def wordOfNat (n : Nat) : Word := BitVec.ofNat 256 n

def roundUp32 (n : Nat) : Nat := (n + 31) / 32 * 32

def byteOfWord (w : Word) (i : Nat) : UInt8 :=
  let shift := 8 * (31 - i)
  UInt8.ofNat (BitVec.toNat (w >>> shift) % 256)

def Mem.grow (m : Mem) (n : Nat) : Mem :=
  let size := Array.size m
  if n ≤ size then m
  else
    let padding := List.toArray (List.replicate (n - size) (0 : UInt8))
    m ++ padding

def Mem.load8 (m : Mem) (a : Word) : UInt8 :=
  Array.getD m (BitVec.toNat a) 0

def Mem.store8 (m : Mem) (a : Word) (b : UInt8) : Mem :=
  let i := BitVec.toNat a
  let grown := Mem.grow m (i + 1)
  Array.set! grown i b

def Mem.loadWord (m : Mem) (a : Word) : Word :=
  let step := fun (acc : Word) (i : Nat) =>
    let byte := Mem.load8 m (a + wordOfNat i)
    (acc <<< 8) ||| BitVec.ofNat 256 (UInt8.toNat byte)
  List.foldl step 0 (List.range 32)

def Mem.storeWord (m : Mem) (a : Word) (w : Word) : Mem :=
  let step := fun (mm : Mem) (i : Nat) =>
    Mem.store8 mm (a + wordOfNat i) (byteOfWord w i)
  List.foldl step m (List.range 32)

def Mem.loadBytes (m : Mem) (a : Word) (n : Nat) : List UInt8 :=
  List.map (fun i => Mem.load8 m (a + wordOfNat i)) (List.range n)

def Mem.storeBytes : Mem → Word → List UInt8 → Mem
  | m, _, [] => m
  | m, a, b :: bs => Mem.storeBytes (Mem.store8 m a b) (a + 1) bs

def bytesToWord (bs : List UInt8) : Word :=
  let step := fun (acc : Word) (b : UInt8) => (acc <<< 8) ||| BitVec.ofNat 256 (UInt8.toNat b)
  List.foldl step 0 bs

def wordToBytes (w : Word) : List UInt8 :=
  List.map (fun i => byteOfWord w i) (List.range 32)

def setByteAt (bs : List UInt8) (i : Nat) (b : UInt8) : List UInt8 :=
  List.mapIdx (fun j x => if j = i then b else x) bs

def setWordAt (bs : List UInt8) (i : Nat) (w : Word) : List UInt8 :=
  let ws := wordToBytes w
  let patch := fun (j : Nat) (x : UInt8) =>
    let inRange := i ≤ j && j < i + 32
    if inRange then List.getD ws (j - i) 0 else x
  List.mapIdx patch bs

def getWordAt (bs : List UInt8) (i : Nat) : Word :=
  let slice := List.map (fun k => List.getD bs (i + k) 0) (List.range 32)
  bytesToWord slice

end AbiModel
