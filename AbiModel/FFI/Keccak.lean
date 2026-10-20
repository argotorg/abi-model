import AbiModel.Word

namespace AbiModel.FFI

/-- Ethereum `keccak256` (original Keccak padding, as the EVM's `KECCAK256`
    opcode — not FIPS-202 SHA3-256), implemented in C via FFI (`c/ffi.c`)
    Being `opaque`, it has no definitional content: proofs can
    only treat it as an uninterpreted function. Evaluating it
    needs the native library, i.e. a compiled executable or a
    module built with `precompileModules`. -/
@[extern "abi_model_keccak256"]
opaque keccak256 (input : @& ByteArray) : ByteArray

/-- Big-endian bytes → word (the EVM reads a hash as a big-endian integer). -/
def wordOfBytesBE (b : ByteArray) : Word :=
  BitVec.ofNat 256 (b.foldl (fun acc x => acc * 256 + x.toNat) 0)

/-- `keccak256` as a 256-bit word, e.g. for a variant tag
    `keccak256("Name(argSigs)")`. -/
def keccakWord (input : ByteArray) : Word := wordOfBytesBE (keccak256 input)

/-- `keccak256` of a string's UTF-8 bytes, as a word. -/
def keccakString (s : String) : Word := keccakWord s.toUTF8

/-- The 4-byte function selector: the top 4 bytes of `keccak256(sig)`. -/
def selector (sig : String) : BitVec 32 := (keccakString sig).extractLsb' 224 32

end AbiModel.FFI
