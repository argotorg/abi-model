# abi-model

A small Lean 4 model of Solcore's ABI encoding/decoding for **algebraic data
types**, aligned with the documentation
(`solcore/doc/src/core/abi-encoding-decoding.md`) and `std/ABIGeneric.solc`,
with a machine-checked **round-trip** theorem.

## What it models

The algebraic core of the ABI type universe, plus **dynamic arrays**, as the doc
describes it:

- products are right-nested `pair`s;
- the primitive **binary sum** `sum f g` (`ABIGeneric.sol`'s `sum<f, g>`), with a
  tag word `0 = inl`, `1 = inr` at every nesting level;
- a derived **multi-constructor enum** `enum n₀ t₀ cs` (`DeriveGeneric.hs`), with
  the same static/dynamic layout as its SOP rep `sum<t₀, sum<t₁, …>>` but a
  *single* tag word `keccak256("Name(argSigs)")` (computed by the FFI
  `keccak256`, signatures in `AbiModel/Sig.lean`);
- `tup` is the ABITuple grouping wrapper;
- **`array a` is a dynamic array** of `a` (element type may itself be dynamic);
- atoms `word`, `bool`, and `unit`.

Encoding is **head/tail canonical**, aligned with the std `ABIEncode.encodeInto`
(`std/std.sol:1365,1458`) and `doc/src/core/abi-encoding-decoding.md`:
`encode t v = encHead t v (headWords t) ++ encTail t v`. A static value is
written inline in the head; a **dynamic node** (array, dynamic sum/tup) writes a
single **offset word** into the head pointing at its `[length | ...]` block in
the shared tail (an array of dynamic elements gets an inner offset table, like
the std `abiArrayGet`). Offsets are **word-indexed** here — the std's byte
offset is `32 ×` this — which keeps the model functional and total without a
byte-level memory. A static `sum` still writes `[tag | branch]` padded to the
widest branch. A dynamic `sum` puts the same padded `[tag | branch head]` block
in the tail, followed by the branch's tail; the branch's offsets are relative to
the tag word, exactly as `ABIGeneric.sol`'s `encodeInto` (`newBase = tail`,
branch at offset 32). The decoder is base-relative (it follows offsets) and
**lenient** on the tag like the real one (`tag = 0 ⇒ inl`, any other ⇒ `inr`).

## The theorems and the checks

`AbiModel/Roundtrip.lean` proves the retraction law (T1) — decoding a canonical
encoding recovers the value — for **every type**, static and dynamic (arrays,
dynamic sums, tuples and enums, with the offset indirection), in the
base-relative model:

```lean
-- static types: no offsets, so no length bound
theorem decode_encode_static (t : Ty) (hst : isStatic t = true) (v : Value t)
    (hfit : Fits t v) : decode t (encode t v) = v

theorem decodeAll_encode_static (t : Ty) (hst : isStatic t = true) (v : Value t)
    (hfit : Fits t v) : decodeAll t (encode t v) = some v

-- all types
theorem decode_encode_fits (t : Ty) (v : Value t) (hfit : Fits t v)
    (hlen : (encode t v).length < 2 ^ 256) : decode t (encode t v) = v

-- dynamic types (the case the offset machinery is for)
theorem decode_encode_dynamic : ∀ (t : Ty), isStatic t = false → ∀ (v : Value t),
    Fits t v → (encode t v).length < 2 ^ 256 → decode t (encode t v) = v
```

The general theorem rests on the placement lemma `decAt_place`: if a value's head
(written with tail cursor `tb`) sits at `base + ho` in the wire and its tail at
`base + tb`, the base-relative decoder recovers the value. That lemma follows each
offset word to the tail block it points at. Its static counterpart `decAt_static`
needs no tail. Both rest on the structural lemmas `encHead_length`,
`encTail_nil_of_static`, `encHead_static_tb_irrel` and `decAt_shift` (decoding is
invariant under prepending a prefix and shifting the base). The enum cases go
through the per-constructor `arm*_of` lemmas.

### Side conditions

`Fits t v` collects the value-level side conditions: array lengths fit in a word,
and every enum on the value's path has pairwise-distinct constructor tags (without
it, e.g. `enum "A" word (last "A" word)` decodes `inr 5` as `inl 5`).

The general and dynamic theorems additionally assume
`(encode t v).length < 2 ^ 256`. Dynamic nodes write their tail position as an
offset *word*, i.e. modulo `2^256`, and the decoder reads it back with `.toNat`; the
round trip holds only if no offset wraps. Every offset points inside the wire, so
bounding the wire's length bounds all of them. Without it, e.g. a
`pair (array word) (array word)` whose first array has more than `2^256` elements
writes a wrapped offset for the second array, which then decodes from the wrong
place. The static theorems need no such bound because static types write no
offsets. The array-length condition in `Fits` is separate: an `array unit` of
length `2^256` has a tiny encoding (zero-width elements) but its length word wraps
to `0`. Neither condition excludes anything real: no calldata or memory comes near
`2^256` bytes.

The converse (a _section_ `encode ∘ decode = id`) is **false** for the lenient
decoder — a non-canonical tag decodes as `inr` (or, for an enum, as the last
constructor) and re-encodes canonically, so the model is deliberately
non-injective, matching the real decoder.

### Assumptions about keccak256

Enum tags come from the FFI `keccak256` (see below), an `opaque` function the
proofs cannot look inside. The theorems therefore hold for **any** function the
opaque constant might denote. Their only assumption about the hash is the
distinct-tags condition in `Fits`:

- **Local collision-freeness.** Only the signature strings `"Name(argSigs)"` of
  the constructors of the enums a value passes through must hash to distinct
  words. This is not a global injectivity assumption about keccak, which would be
  false (all byte strings map to 256 bits) and, as an axiom, inconsistent. It
  holds when the signatures are distinct (solcore rejects duplicate constructor
  names) and keccak has no collision among them, the standard cryptographic
  assumption.
- **No new axioms.** The assumption is a hypothesis of the theorems, not an
  axiom: `#print axioms` lists only `propext`, `Classical.choice` and
  `Quot.sound`.
- **Checking it needs native code.** Because the function is opaque, the
  condition can't be discharged by `decide`. For concrete enums it is checked by
  evaluating the FFI natively, which trusts the C implementation (SHA3IUF) and
  its agreement with EVM Keccak, as tested by the known answers in
  `AbiTest/Keccak.lean`.

### Concrete checks

`AbiModel/Sanity.lean` complements the theorems with a battery of `#guard`s, each
of which fails at elaboration unless it holds: round trips on concrete values and
exact wire layouts. Checks involving enums evaluate tags, i.e. the FFI, so they
live in the natively compiled `AbiTest` library: `AbiTest/Enum.lean` checks enum
round trips and wires, including the wire of solcore's `rtS2` test and the tags
and selector from solcore's test expectations. `AbiTest/Keccak.lean` checks the
FFI `keccak256` against OpenSSL known answers. The whole project builds with
**no `sorry`**.

## Layout

| file                      | contents                                                  |
| ------------------------- | --------------------------------------------------------- |
| `AbiModel/Word.lean`      | `Word := BitVec 256`, `Wire := List Word`                 |
| `AbiModel/Ty.lean`        | `Ty`/`Ctors` (+ `array`, `enum`), `isStatic`, `headWords` |
| `AbiModel/Val.lean`       | `Value : Ty → Type` (dependent; `array a ↦ List`)         |
| `AbiModel/Sig.lean`       | ABI signature strings (`sigStr`) and enum tags (`ctorTag`) |
| `AbiModel/Encode.lean`    | head/tail `encode` with word offsets (`encHead`/`encTail`) |
| `AbiModel/Decode.lean`    | base-relative `decode` following offsets (`decAt`/`decSeq`)|
| `AbiModel/Check.lean`     | `rt`/`wireIs` Boolean checks used by the `#guard`s         |
| `AbiModel/Roundtrip.lean` | round-trip theorems (T1), static and dynamic, + lemmas    |
| `AbiModel/Sanity.lean`    | `#guard` round-trip and exact-wire battery                |
| `AbiModel/FFI/Keccak.lean` | `keccak256` via FFI (+ `keccakWord`, `selector`)            |
| `c/ffi.c`, `c/sha3/`       | C glue + SHA3IUF (Keccak)                                   |
| `AbiTest/Keccak.lean`      | keccak `#guard` known-answer tests (`precompileModules`)    |
| `AbiTest/Enum.lean`        | enum `#guard`s: tags, wires, round trips (`precompileModules`) |
| `Main.lean`               | a wire-level round-trip sanity check                      |

## keccak256 (FFI)

`AbiModel.FFI.keccak256 : ByteArray → ByteArray` is Ethereum's Keccak-256
(original padding, as the `KECCAK256` opcode, not FIPS SHA3-256), implemented in
C following the approach of EVMYulLean's `EvmYul/FFI`. It is `opaque`, so proofs
see it as an uninterpreted function. The interpreter cannot call it, so
`#eval`/`#guard` on it only work in modules built with
`precompileModules := true`: the `AbiTest` library (`AbiTest/Keccak.lean`) holds
its known-answer `#guard`s, checked against `openssl dgst -keccak-256`, and the
enum checks that evaluate tags (`AbiTest/Enum.lean`), and is part of `lake build`.
`AbiTest` imports `AbiModel.Check` rather than `AbiModel.Sanity`: loading
`Sanity`'s native code into the elaborator crashes it (exit 139).


## Build & run

```sh
lake build        # compiles all modules incl. the theorems (no sorry)
lake exe abitest  # runs the sample round-trip check
```
