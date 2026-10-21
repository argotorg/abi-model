# abi-model

A Lean 4 model of Solcore's ABI encoding/decoding for **algebraic data types**,
aligned with the documentation (`solcore/doc/src/core/abi-encoding-decoding.md`)
and the std library (`std/std.sol`, `std/ABIGeneric.solc`). The project has two
parts:

1. a **verified model**: an encoder, a decoder and machine-checked
   **round-trip** theorems (no `sorry`);
2. a **differential test harness** that compiles Solcore contracts generated
   from the model, runs them on the EVM and compares the bytes Solcore produces
   with the model's prediction.

## What it models

The type universe (`AbiModel/Ty.lean`) is the algebraic core of the ABI plus
dynamic arrays:

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

Values are given by a dependent `Value : Ty → Type` (`AbiModel/Val.lean`).

Encoding is **head/tail canonical**, aligned with the std `ABIEncode.encodeInto`:
`encode t v = encHead t v (headWords t) ++ encTail t v`.

- A static value is written inline in the head.
- A **dynamic node** (array, dynamic sum, enum, or dynamic `tup`) writes one **offset
  word** into the head. The offset points at the node's block in the shared
  tail. An array of dynamic elements gets an inner offset table, like the std
  `abiArrayGet`.
- A static `sum` writes `[tag | branch]`, padded to the widest branch.
- A dynamic `sum` puts the same padded `[tag | branch head]` block in the tail,
  followed by the branch's tail. The branch's offsets are relative to the tag
  word, as in `ABIGeneric.sol`'s `encodeInto` (`newBase = tail`, branch at
  offset 32).

Offsets are **word-indexed** in `encode`; the std's byte offset is `32 ×` this.
`AbiModel/EncodeAnn.lean` gives the byte-level wire (`encodeBytes`) and proves it
equal to `encode` at unit scale (`encodeAnn_one`).

The decoder is base-relative (it follows offsets), total (out-of-bounds reads
give `0`) and **lenient** on tags like the real one: `tag = 0` means `inl`, any
other value means `inr`.


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

## Project layout

| path                       | contents                                                         |
| -------------------------- | ---------------------------------------------------------------- |
| `AbiModel/Word.lean`       | `Word := BitVec 256`, `Wire := List Word`                        |
| `AbiModel/Ty.lean`         | `Ty`/`Ctors` (+ `array`, `enum`), `isStatic`, `headWords`        |
| `AbiModel/Val.lean`        | `Value : Ty → Type` (dependent; `array a ↦ List`)                |
| `AbiModel/Sig.lean`        | ABI signature strings (`sigStr`) and enum tags (`ctorTag`)       |
| `AbiModel/Encode.lean`     | head/tail `encode` with word offsets (`encHead`/`encTail`)       |
| `AbiModel/EncodeAnn.lean`  | byte-offset encoder with word roles (`encodeBytes`)              |
| `AbiModel/Decode.lean`     | base-relative `decode` following offsets (`decAt`/`decSeq`)      |
| `AbiModel/Check.lean`      | `rt`/`wireIs` Boolean checks used by the `#guard`s               |
| `AbiModel/Roundtrip.lean`  | round-trip theorems (T1), static and dynamic, and their lemmas   |
| `AbiModel/Sanity.lean`     | `#guard` round-trip and exact-wire battery                       |
| `AbiModel/FFI/Keccak.lean` | `keccak256` via FFI (`keccakWord`, `selector`)                   |
| `c/ffi.c`, `c/sha3/`       | C glue and the vendored SHA3IUF Keccak implementation            |
| `AbiTest/Keccak.lean`      | Keccak known-answer `#guard`s (`precompileModules`)              |
| `AbiTest/Enum.lean`        | enum `#guard`s: tags, wires, round trips (`precompileModules`)   |
| `AbiDiff/Solc.lean`        | renders a case as Solcore source and as the runner's JSON test   |
| `AbiDiff/Cases.lean`       | hand-picked cases, one per layout rule                           |
| `AbiDiff/Gen.lean`         | Plausible generators and shrinkers for random cases              |
| `AbiDiff/Runner.lean`      | runs batches through Solcore, bisects compile failures, shrinks  |
| `AbiDiff/Report.lean`      | the Markdown report (`out/report.md`)                            |
| `AbiDiff/Main.lean`        | `abidiff` command-line entry point                               |
| `Main.lean`                | `abitest`: a small wire-level round-trip check                   |
| `scripts/diff-solcore.sh`  | builds and runs `abidiff`                                        |
| `scripts/run-solcore.sh`   | compiles one generated contract and runs its tests               |
| `flake.nix`, `flake.lock`  | pins Solcore and the tools the differential test needs           |
| `.github/workflows/`       | CI: `lake build`, and the differential test against Solcore      |

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

Lake targets (`lakefile.lean`):

| target      | kind    | notes                                                           |
| ----------- | ------- | --------------------------------------------------------------- |
| `AbiModel`  | library | the model and the theorems                                      |
| `AbiTest`   | library | `precompileModules := true`, so `#guard`s can call the FFI      |
| `AbiDiff`   | library | the differential harness                                        |
| `libabiffi` | C lib   | `c/ffi.c` + `c/sha3/sha3.c`, linked into the targets above      |
| `abitest`   | exe     | `Main.lean`; also the `lake test` driver                        |
| `abidiff`   | exe     | `AbiDiff/Main.lean`                                             |

## Dependencies

**Lean side**

- Lean `v4.33.0` (pinned in `lean-toolchain`; `elan` installs it).
- [Plausible](https://github.com/leanprover-community/plausible) `v4.33.0`, for
  random generation and shrinking (pinned in `lake-manifest.json`).
- A C compiler (`cc`), to build the Keccak FFI library.

**Differential test** (all provided by `flake.nix`)

- [Solcore](https://github.com/argotorg/solcore), from the flake input `solcore`
  (pinned in `flake.lock`). It provides `sol-core` and `yule` (compiler),
  `testrunner` (test runner), `evmone` (EVM) and the `std` library sources.
- `solc` (compiles the generated Yul to bytecode), `jq`, `git`, `elan`,
  `coreutils`.

The flake exports three variables used by the scripts: `SOLCORE_SRC` (the
Solcore sources, for `std`), `SOLCORE_REV` (the pinned revision, shown in the
report) and `EVMONE` (path to `libevmone`).

## Building and the Lean checks

Without Nix, with `elan` and a C compiler installed:

```sh
lake build   # the model, the theorems, the #guard batteries and AbiDiff
lake test    # runs abitest (exit code 0 on success)
```

`lake build` is itself a test: the theorems are checked, and each `#guard` in
`AbiModel/Sanity.lean`, `AbiTest/Keccak.lean`, `AbiTest/Enum.lean` and
`AbiDiff/Gen.lean` fails the build if it does not hold.

With Nix, the same commands work inside the development shell:

```sh
nix develop
lake build
lake test
```

## Differential tests against Solcore (Nix)

For each case (a model type and a value of it), `abidiff` generates a Solcore
method returning `abi_encode(v)` and a test file whose expected return data is
the model's prediction (`encodeBytes`). The contracts are compiled with
`sol-core`, `yule` and `solc` and run with Solcore's `testrunner` on evmone.

Run from the repository root:

```sh
nix run .#diff                                 # the fixed cases (AbiDiff/Cases.lean)
nix run .#diff -- --random --seed 7 --n 100    # 100 random cases, shrunk on failure
nix run .#diff -- --help                       # all options
```

Options (everything after `--` is passed to `abidiff`):

| option        | default | meaning                                              |
| ------------- | ------- | ---------------------------------------------------- |
| `--random`    | off     | random cases instead of the fixed ones               |
| `--seed S`    | clock   | seed for the random cases (same seed, same cases)    |
| `--n N`       | 50      | number of random cases                               |
| `--depth D`   | 3       | maximum depth of the generated types                 |
| `--batch B`   | 25      | cases per compiled contract                          |
| `--no-shrink` | off     | do not shrink diverging random cases                 |
| `--out DIR`   | `out`   | output directory                                     |

Set `SOLC_OPTIMIZE=1` to compile with the `solc` optimizer (it only changes
gas, and it is slow on large batches).

Choosing the Solcore revision:

```sh
nix run .#diff --override-input solcore github:argotorg/solcore   # current Solcore main
nix run .#diff --override-input solcore path:../solcore           # a local checkout
nix flake update solcore                                          # move the pin to main
```

Inside `nix develop` the driver can also be run directly:
`scripts/diff-solcore.sh [options]`.

### Results

Each case ends as:

- **agree**: Solcore returned exactly the predicted bytes;
- **diverge**: Solcore returned other bytes, or reverted. Random cases are
  shrunk with Plausible's `Shrinkable`;
- **compile-fail**: Solcore rejected the generated source. A batch that does not
  compile is bisected to find the offending cases.

The output directory contains:

- `report.md`: a summary per area (static, dynamic, arrays, sums, `ABITuple`),
  and for each divergence the generated source and a word-by-word table, with
  every word labelled offset / tag / length / data / padding;
- `regressions/`: a `.sol` + `.json` pair for each divergence, in the format of
  Solcore's `test/examples/dispatch/` tests;
- `batches/`: the generated contracts, test files and compiler logs.

`abidiff` exits with `1` if any case diverges or fails to compile.

Random cases are generated type-first from the fragment the std can encode
(`AbiDiff.supported`; arrays are restricted to `memory<DynArray<uint256>>`), so
the generated Solcore is well typed by construction.

## Bugs found

Bugs in Solcore found by the differential tests:

| #   | Solcore rev | Component                                    | Symptom                                                                                                                                                        | Found by                                                     | Status                                                                      |
| --- | ----------- | -------------------------------------------- | -------------------------------------------------------------------------------------------------------------------------------------------------------------- | ------------------------------------------------------------ | --------------------------------------------------------------------------- |
| 1   | `a7b7afb`   | `ABIEncode<ABITuple<tuple>>` (`std/std.sol`) | A dynamic `ABITuple` writes its offset to `basePtr` instead of `basePtr + offset`, overwriting the first word of the enclosing region (a field, or a sum's tag) | `nix run .#diff` (fixed cases; random cases with `--seed 2`) | One-line fix and regression tests on `fix/abituple-head-offset`, not merged |

## Continuous integration

- `lean_action_ci.yml`: `lake build` on every push and pull request.
- `solcore_diff.yml`: the fixed cases and 100 random cases (seeded with the run
  number) against the pinned Solcore on every push and pull request. Weekly and
  manual runs also test the current Solcore main. The reports go to the job
  summary, and the reports, regressions and batches are uploaded as artifacts.
