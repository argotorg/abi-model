import AbiDiff.Cases
import AbiDiff.Gen
import AbiDiff.Report

open AbiDiff

structure Opts where
  random : Bool := false
  seed : Option Nat := none
  n : Nat := 50
  depth : Nat := 3
  out : String := "out"
  shrink : Bool := true
  batch : Nat := 25

def usage : String :=
"usage: abidiff [--random] [--seed S] [--n N] [--depth D] [--out DIR] [--batch B] [--no-shrink]

Generates Solcore contracts from the Lean ABI model, runs them with Solcore
(scripts/run-solcore.sh) and writes DIR/report.md. Without --random it runs the
fixed cases of AbiDiff/Cases.lean. Exits 1 if any case diverges or fails to
compile. Needs SOLCORE_SRC and EVMONE (nix develop, or nix run .#diff)."

partial def parseArgs (o : Opts) : List String → Except String Opts
  | [] => .ok o
  | "--random" :: r => parseArgs { o with random := true } r
  | "--no-shrink" :: r => parseArgs { o with shrink := false } r
  | "--seed" :: v :: r => do parseArgs { o with seed := some (← nat v) } r
  | "--n" :: v :: r => do parseArgs { o with n := ← nat v } r
  | "--depth" :: v :: r => do parseArgs { o with depth := ← nat v } r
  | "--batch" :: v :: r => do parseArgs { o with batch := max 1 (← nat v) } r
  | "--out" :: v :: r => parseArgs { o with out := v } r
  | a :: _ => .error s!"unknown argument: {a}"
where
  nat (v : String) : Except String Nat := match v.toNat? with
    | some n => .ok n
    | none => .error s!"not a number: {v}"

def chunks (k : Nat) (xs : List α) : List (List α) :=
  if _h : k = 0 ∨ xs = [] then [xs].filter (!·.isEmpty)
  else xs.take k :: chunks k (xs.drop k)
termination_by xs.length
decreasing_by simp_wf; cases xs <;> simp_all; omega

def cmdOut (cmd : String) (args : Array String) : IO String := do
  try
    let o ← IO.Process.output { cmd, args }
    return if o.exitCode == 0 then o.stdout.trimAscii.toString else "unknown"
  catch _ => return "unknown"

def main (args : List String) : IO UInt32 := do
  if args.contains "--help" then IO.println usage; return 0
  let o ← match parseArgs {} args with
    | .ok o => pure o
    | .error e => IO.eprintln s!"{e}\n\n{usage}"; return 2
  let dir : System.FilePath := o.out
  -- start from a clean output directory, but only delete one we created
  if ← (dir / ".abidiff").pathExists then IO.FS.removeDirAll dir
  IO.FS.createDirAll (dir / "batches")
  IO.FS.writeFile (dir / ".abidiff") ""
  let ctx : Ctx := { dir := dir / "batches", counter := ← IO.mkRef 0 }

  let seed ← match o.seed with
    | some s => pure s
    | none => pure ((← IO.monoNanosNow) % 1000000007)
  let (cases, mode) ← if o.random then
      match sampleCases seed o.n o.depth with
      | .ok cs => pure (cs, s!"random, seed `{seed}`, N = {o.n}, depth {o.depth}")
      | .error e => IO.eprintln s!"generation failed: {e}"; return 2
    else pure (fixedCases, s!"fixed cases ({fixedCases.length})")
  IO.println s!"abidiff: {mode}"

  let numbered := cases.zipIdx.map fun (c, i) => (i, c)
  -- compile time grows faster than linearly with contract size, so run in batches
  let mut outcomes : List Outcome := []
  for chunk in chunks o.batch numbered do
    outcomes := outcomes ++ (← runCases ctx chunk)
  let mut results : List Result := []
  for ((i, c), oc) in numbered.zip outcomes do
    let mut r : Result := { id := i, case := c, outcome := oc }
    if oc.isDiverge then
      let (fc, _) ← if o.random && o.shrink then do
          let (fc, fo, steps) ← shrinkLoop ctx c oc
          r := { r with shrunk := some (fc, fo, steps) }
          pure (fc, fo)
        else pure (c, oc)
      let name := s!"case{i}"
      writeBatch (dir / "regressions") name [(0, fc)]
      r := { r with regression := some (dir / "regressions" / s!"{name}.\{sol,json}").toString }
    results := results ++ [r]

  let solc ← cmdOut "solc" #["--version"]
  let info : Meta := {
    solcore := (← IO.getEnv "SOLCORE_REV").getD "unknown"
    abiModel := ← cmdOut "git" #["rev-parse", "--short", "HEAD"]
    mode := mode
    date := ← cmdOut "date" #["-u", "+%Y-%m-%d %H:%M UTC"]
    solc := ((solc.splitOn "\n").getLast?.getD solc)
  }
  IO.FS.writeFile (dir / "report.md") (report info results)

  let bad := results.filter (!·.outcome.isAgree)
  IO.println s!"abidiff: {results.length - bad.length}/{results.length} agree; report in {dir / "report.md"}"
  return if bad.isEmpty then 0 else 1
