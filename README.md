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
  *single* tag word `keccak256("Name(argSigs)")` (computed in Lean:
  `AbiModel/Keccak.lean`, signatures in `AbiModel/Sig.lean`);
- `tup` is the ABITuple grouping wrapper;
- **`array a` is a dynamic array** of `a` (element type may itself be dynamic);
- atoms `word`, `bool`, and `unit`.

Encoding is **head/tail canonical**, aligned with the std `ABIEncode.encodeInto`
(`std/std.sol:1365,1458`) and `doc/src/core/abi-encoding-decoding.md`:
`encode t v = encHead t v (headWords t) ++ encTail t v`. A static value is written
inline in the head; a **dynamic node** (array, dynamic sum/tup) writes a single
**offset word** into the head pointing at its `[length | ...]` block in the shared
tail (an array of dynamic elements gets an inner offset table, like the std
`abiArrayGet`). Offsets are **word-indexed** here — the std's byte offset is
`32 ×` this — which keeps the model functional and total without a byte-level
memory. A static `sum` still writes `[tag | branch]` padded to the widest branch.
A dynamic `sum` puts the same padded `[tag | branch head]` block in the tail,
followed by the branch's tail; the branch's offsets are relative to the tag word,
exactly as `ABIGeneric.sol`'s `encodeInto` (`newBase = tail`, branch at offset 32).
The decoder is base-relative (it follows offsets) and **lenient** on the tag like
the real one (`tag = 0 ⇒ inl`, any other ⇒ `inr`).

## The theorem and the checks

`AbiModel/Roundtrip.lean` proves the retraction law (T1) for the **static
fragment** — decoding a canonical encoding recovers the value — in the new
base-relative model:

```lean
theorem decode_encode_static (t : Ty) (hst : isStatic t = true) (v : Value t)
    (hfit : Fits t v) : decode t (encode t v) = v

theorem decodeAll_encode_static (t : Ty) (hst : isStatic t = true) (v : Value t)
    (hfit : Fits t v) : decodeAll t (encode t v) = some v
```

`Fits t v` collects the side conditions: array lengths fit in a word, and every
enum on the value's path has pairwise-distinct constructor tags (in solcore,
distinct constructor names make a violation a keccak collision).

The general `decode_encode_fits` (and `decode_encode_dynamic`) additionally assume
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

alongside the structural lemmas the dynamic machinery rests on (`encHead_length`,
`encTail_nil_of_static`, `encHead_static_tb_irrel`). The converse (a _section_
`encode ∘ decode = id`) is **false** for the lenient decoder — a non-canonical tag
decodes as `inr` and re-encodes to `1`, so the model is deliberately non-injective,
matching the real decoder.

**Dynamic arrays** (including arrays of arrays and dynamic sums, with the offset
indirection) are validated by a **machine-checked round-trip battery** in
`AbiModel/Sanity.lean`: each `#guard` fails at elaboration unless the concrete
round-trip holds, so it is a real check with no `sorry`. Extending the universal
`decode_encode` proof across the offset indirection (and its `2^256` bounds) is the
remaining step; nothing is admitted in the meantime — the whole project builds with
**no `sorry`**.

## Layout

| file                      | contents                                                  |
| ------------------------- | --------------------------------------------------------- |
| `AbiModel/Word.lean`      | `Word := BitVec 256`, `Wire := List Word`                 |
| `AbiModel/Ty.lean`        | `Ty` (+ `array`), `isStatic`, `headWords`                 |
| `AbiModel/Val.lean`       | `Value : Ty → Type` (dependent; `array a ↦ List`)         |
| `AbiModel/Encode.lean`    | head/tail `encode` with word offsets (`encHead`/`encTail`) |
| `AbiModel/Decode.lean`    | base-relative `decode` following offsets (`decAt`/`decSeq`)|
| `AbiModel/Roundtrip.lean` | `decode_encode_static` (T1) + structural lemmas           |
| `AbiModel/Sanity.lean`    | `#guard` round-trip battery for dynamic arrays            |
| `Main.lean`               | a wire-level round-trip sanity check                      |

## Build & run

```sh
lake build        # compiles all modules incl. the theorems (no sorry)
lake exe abitest  # runs the sample round-trip check
```
