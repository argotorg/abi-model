import Lean.Data.Json
import Plausible
import AbiDiff.Gen

/-!
Running batches of cases through Solcore (`scripts/run-solcore.sh`) and reading
back the test runner's verdict for each one.
-/

namespace AbiDiff
open Lean

inductive Outcome where
  /-- Solcore returned exactly the bytes the model predicts. -/
  | agree
  /-- The call returned other bytes (`actual`, or `"failure"` on revert). -/
  | diverge (actual : String) (message : String)
  /-- Solcore rejected the generated source. -/
  | compileFail (error : String)

def Outcome.isAgree : Outcome → Bool | .agree => true | _ => false
def Outcome.isDiverge : Outcome → Bool | .diverge .. => true | _ => false

structure Ctx where
  dir : System.FilePath
  counter : IO.Ref Nat

def writeBatch (dir : System.FilePath) (name : String) (cases : List (Nat × Case)) : IO Unit := do
  IO.FS.createDirAll dir
  IO.FS.writeFile (dir / s!"{name}.sol") (solContract cases)
  IO.FS.writeFile (dir / s!"{name}.json") (testJson name cases)

/-- `(message, actual)` for each test of the (single) suite in a runner result file. -/
def parseResults (s : String) : Except String (List (String × String)) := do
  let j ← Json.parse s
  let obj ← j.getObj?
  let some suite := obj.toList.head? | throw "empty runner result"
  let recs ← suite.2.getArr?
  recs.toList.mapM fun r => do
    return (← r.getObjValAs? String "message", (r.getObjValAs? String "actual").toOption.getD "")

/-- Compile and run one batch. `.error` carries the compiler's diagnostics. -/
def runOnce (ctx : Ctx) (cases : List (Nat × Case)) : IO (Except String (List Outcome)) := do
  let k ← ctx.counter.modifyGet fun n => (n, n + 1)
  let name := s!"batch{k}"
  writeBatch ctx.dir name cases
  let input := ctx.dir / s!"{name}.json"
  let output := ctx.dir / s!"{name}.out.json"
  let out ← IO.Process.output
    { cmd := "scripts/run-solcore.sh", args := #[input.toString, output.toString] }
  if out.exitCode == 3 then return .error out.stderr
  if out.exitCode != 0 then
    throw <| IO.userError s!"run-solcore.sh failed with code {out.exitCode}:\n{out.stderr}"
  match parseResults (← IO.FS.readFile output) with
  | .error e => throw <| IO.userError s!"cannot read {output}: {e}"
  | .ok [] => throw <| IO.userError s!"no results in {output}"
  | .ok ((msg, _) :: calls) =>
    if msg != "Creation succeeded." then
      return .ok (cases.map fun _ => .diverge "" s!"constructor: {msg}")
    if calls.length != cases.length then
      throw <| IO.userError s!"{output}: expected {cases.length} results, got {calls.length}"
    return .ok (calls.map fun (m, a) => if m == "Passed." then .agree else .diverge a m)

/-- Run cases in one contract; if it does not compile, bisect to find the
    offending cases and run the rest. -/
partial def runCases (ctx : Ctx) (cases : List (Nat × Case)) : IO (List Outcome) := do
  if cases.isEmpty then return []
  match ← runOnce ctx cases with
  | .ok os => return os
  | .error err =>
    if cases.length == 1 then return [.compileFail err]
    let (l, r) := cases.splitAt (cases.length / 2)
    return (← runCases ctx l) ++ (← runCases ctx r)

/-- Greedy shrinking: each round runs every shrink candidate in one batch and
    continues from the first that still diverges. Returns the smallest diverging
    case, its outcome, and the number of successful steps. -/
partial def shrinkLoop (ctx : Ctx) (c : Case) (o : Outcome) (steps : Nat := 0) :
    IO (Case × Outcome × Nat) := do
  let cands := Plausible.Shrinkable.shrink c
  if steps ≥ 40 || cands.isEmpty then return (c, o, steps)
  let outs ← runCases ctx (cands.zipIdx.map fun (c, i) => (i, c))
  match (cands.zip outs).find? (·.2.isDiverge) with
  | some (c', o') => shrinkLoop ctx c' o' (steps + 1)
  | none => return (c, o, steps)

end AbiDiff
