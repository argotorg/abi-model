import AbiModel.FFI.Keccak

/-!
Known-answer tests for the FFI `keccak256` (Ethereum Keccak, not SHA3-256).
Expected values were computed independently with `openssl dgst -keccak-256`.

`AbiModel.FFI.keccak256` is `@[extern]`, so these `#guard`s only elaborate
because the `AbiTest` library is built with `precompileModules := true`, which
makes Lake load the native `libabiffi` into the elaborator.
-/

namespace AbiTest
open AbiModel.FFI

def aStr (n : Nat) : String := String.ofList (List.replicate n 'a')

-- keccak256("") — SHA3-256("") would be a7ffc6f8…
#guard keccakString "" ==
  0xc5d2460186f7233c927e7db2dcc703c0e500b653ca82273b7bfad8045d85a470#256

#guard keccakString "abc" ==
  0x4e03657aea45a94fc7d47ba826c8d667c0d1e6e33a64a036ec44f58fa12d6c45#256

-- padding edge cases around the 136-byte rate
#guard keccakString (aStr 135) ==
  0x34367dc248bbd832f4e3e69dfaac2f92638bd0bbd18f2912ba4ef454919cf446#256
#guard keccakString (aStr 136) ==
  0xa6c4d403279fe3e0af03729caada8374b5ca54d8065329a3ebcaeb4b60aa386e#256

-- more than one sponge block
#guard keccakString (aStr 200) ==
  0x96ea54061def936c4be90b518992fdc6f12f535068a256229aca54267b4d084d#256

#guard (keccak256 (aStr 200).toUTF8).size == 32

-- full hashes of function signatures, and their 4-byte selectors
#guard keccakString "transfer(address,uint256)" ==
  0xa9059cbb2ab09eb219583f4a59a5d0623ade346d962bcd4e46b11da047c9049b#256
#guard keccakString "balanceOf(address)" ==
  0x70a08231b98ef4ca268c9cc3f6b4590e4bfec28280db06bb5d45e689f2a360be#256
#guard selector "transfer(address,uint256)" == 0xa9059cbb#32
#guard selector "balanceOf(address)" == 0x70a08231#32

end AbiTest
