import AbiModel.Word

namespace AbiModel.Keccak

/-!
Keccak-256 (the original Keccak padding `0x01`, as the EVM's `KECCAK256` and
solcore's `keccakLit`; *not* FIPS-202 SHA3-256). Pure Lean, on 25 `UInt64` lanes.
-/

/-- Round constants of Keccak-f[1600]. -/
def roundConsts : Array UInt64 := #[
  0x0000000000000001, 0x0000000000008082, 0x800000000000808A, 0x8000000080008000,
  0x000000000000808B, 0x0000000080000001, 0x8000000080008081, 0x8000000000008009,
  0x000000000000008A, 0x0000000000000088, 0x0000000080008009, 0x000000008000000A,
  0x000000008000808B, 0x800000000000008B, 0x8000000000008089, 0x8000000000008003,
  0x8000000000008002, 0x8000000000000080, 0x000000000000800A, 0x800000008000000A,
  0x8000000080008081, 0x8000000000008080, 0x0000000080000001, 0x8000000080008008]

/-- Rotation offsets, indexed by lane `x + 5 * y`. -/
def rotOffsets : Array UInt64 := #[
   0,  1, 62, 28, 27,
  36, 44,  6, 55, 20,
   3, 10, 43, 25, 39,
  41, 45, 15, 21,  8,
  18,  2, 61, 56, 14]

@[inline] def rotl (x n : UInt64) : UInt64 :=
  if n == 0 then x else (x <<< n) ||| (x >>> (64 - n))

/-- One round of Keccak-f[1600] (θ, ρ, π, χ, ι). -/
def round (a : Array UInt64) (rc : UInt64) : Array UInt64 := Id.run do
  -- θ
  let c := Array.ofFn (n := 5) fun x =>
    a[x.val]! ^^^ a[x.val + 5]! ^^^ a[x.val + 10]! ^^^ a[x.val + 15]! ^^^ a[x.val + 20]!
  let d := Array.ofFn (n := 5) fun x =>
    c[(x.val + 4) % 5]! ^^^ rotl c[(x.val + 1) % 5]! 1
  let a := Array.ofFn (n := 25) fun i => a[i.val]! ^^^ d[i.val % 5]!
  -- ρ and π: B[y, 2x + 3y] = rotl(A[x, y], r[x, y])
  let mut b : Array UInt64 := Array.replicate 25 0
  for x in [0:5] do
    for y in [0:5] do
      b := b.set! (y + 5 * ((2 * x + 3 * y) % 5)) (rotl a[x + 5 * y]! rotOffsets[x + 5 * y]!)
  -- χ
  let a := Array.ofFn (n := 25) fun i =>
    let x := i.val % 5
    let y := i.val / 5
    b[i.val]! ^^^ ((~~~ b[(x + 1) % 5 + 5 * y]!) &&& b[(x + 2) % 5 + 5 * y]!)
  -- ι
  return a.set! 0 (a[0]! ^^^ rc)

def keccakF (a : Array UInt64) : Array UInt64 := roundConsts.foldl round a

/-- Rate of Keccak-256, in bytes (1600 - 2·256 bits). -/
def rate : Nat := 136

/-- Little-endian lane from 8 bytes starting at `off`. -/
def lane (bs : ByteArray) (off : Nat) : UInt64 :=
  (List.range 8).foldr (fun j acc => (acc <<< 8) ||| (bs.get! (off + j)).toUInt64) 0

/-- Keccak-256 digest (32 bytes, as a big-endian byte list). -/
def keccak256 (msg : ByteArray) : List UInt8 := Id.run do
  -- pad10*1 with the Keccak domain byte 0x01
  let padLen := rate - msg.size % rate
  let padded :=
    if padLen == 1 then msg.push 0x81
    else (msg.push 0x01 ++ ByteArray.mk (Array.replicate (padLen - 2) 0)).push 0x80
  let mut st : Array UInt64 := Array.replicate 25 0
  for blk in [0:padded.size / rate] do
    for i in [0:rate / 8] do
      st := st.set! i (st[i]! ^^^ lane padded (blk * rate + 8 * i))
    st := keccakF st
  return (List.range 4).flatMap fun i =>
    (List.range 8).map fun j => (st[i]! >>> (8 * j).toUInt64).toUInt8

end Keccak

/-- Big-endian bytes as a word (the EVM's `mload` of a hash). -/
def wordOfBytes (bs : List UInt8) : Word :=
  BitVec.ofNat 256 (bs.foldl (fun acc b => acc * 256 + b.toNat) 0)

/-- `keccak256` of a string's UTF-8 bytes, as a word (solcore's `keccakLit`). -/
def keccakWord (s : String) : Word := wordOfBytes (Keccak.keccak256 s.toUTF8)

-- standard test vectors
#guard keccakWord "" =
  0xc5d2460186f7233c927e7db2dcc703c0e500b653ca82273b7bfad8045d85a470#256
#guard keccakWord "abc" =
  0x4e03657aea45a94fc7d47ba826c8d667c0d1e6e33a64a036ec44f58fa12d6c45#256
-- padding boundaries (single 0x81 pad byte; a full extra pad block) and a
-- multi-block input; expected values from `openssl dgst -keccak-256`
#guard keccakWord (String.ofList (List.replicate 135 'a')) =
  0x34367dc248bbd832f4e3e69dfaac2f92638bd0bbd18f2912ba4ef454919cf446#256
#guard keccakWord (String.ofList (List.replicate 136 'a')) =
  0xa6c4d403279fe3e0af03729caada8374b5ca54d8065329a3ebcaeb4b60aa386e#256
#guard keccakWord (String.ofList (List.replicate 200 'a')) =
  0x96ea54061def936c4be90b518992fdc6f12f535068a256229aca54267b4d084d#256

end AbiModel
