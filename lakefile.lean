import Lake
open Lake DSL System

package «abi-model» where
  testDriver := "abitest"

require plausible from git
  "https://github.com/leanprover-community/plausible" @ "v4.33.0"

/-- The vendored Keccak implementation (SHA3IUF, see `c/sha3/SOURCE`). -/
def sha3Dir (pkg : Package) : FilePath := pkg.dir / "c" / "sha3"

target sha3.o pkg : FilePath := do
  let oFile := pkg.buildDir / "c" / "sha3.o"
  let srcJob ← inputTextFile <| sha3Dir pkg / "sha3.c"
  buildO oFile srcJob #["-I", (sha3Dir pkg).toString] #["-fPIC", "-O2"] "cc" getLeanTrace

target ffi.o pkg : FilePath := do
  let oFile := pkg.buildDir / "c" / "ffi.o"
  let srcJob ← inputTextFile <| pkg.dir / "c" / "ffi.c"
  let weakArgs := #["-I", (← getLeanIncludeDir).toString, "-I", (sha3Dir pkg).toString]
  buildO oFile srcJob weakArgs #["-fPIC", "-O2"] "cc" getLeanTrace

extern_lib libabiffi pkg := do
  let sha3O ← sha3.o.fetch
  let ffiO ← ffi.o.fetch
  buildStaticLib (pkg.staticLibDir / nameToStaticLib "abiffi") #[sha3O, ffiO]

@[default_target]
lean_lib AbiModel

/-- Tests that evaluate FFI functions in `#guard`s. `precompileModules` compiles
    these modules to native code and loads the package's `extern_lib` into the
    elaborator, which the interpreter cannot otherwise call. -/
@[default_target]
lean_lib AbiTest where
  precompileModules := true

lean_exe abitest where
  root := `Main
