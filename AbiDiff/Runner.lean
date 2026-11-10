import Lean.Data.Json
import Plausible
import AbiDiff.Gen

/-!
Running batches of cases through solcore-rs (`scripts/run-solcore-rs.sh`) on
Anvil, and comparing each call's result with the model's prediction.
-/

namespace AbiDiff
open Lean

/-- What a call checks: `caseI()` the encoder, `echoI(v)` the decoder. -/
inductive Check where
  | encode
  | echo
deriving BEq

inductive Outcome where
  /-- solcore-rs returned exactly the bytes the model predicts. -/
  | agree
  /-- A call returned other bytes (`actual`, or `"failure"` on revert). -/
  | diverge (check : Check) (actual : String) (message : String)
  /-- solcore-rs rejected the generated source. -/
  | compileFail (error : String)

def Outcome.isAgree : Outcome → Bool | .agree => true | _ => false
def Outcome.isDiverge : Outcome → Bool | .diverge .. => true | _ => false

structure Ctx where
  dir : System.FilePath
  counter : IO.Ref Nat
  /-- JSON-RPC URL of the Anvil node the calls run on. -/
  rpc : String

/-- Write a batch as `dir/name/main.sol` (a solcore-rs E2E fixture) and
    `dir/name/calls` (the runner's calldata). Returns the source path. -/
def writeBatch (dir : System.FilePath) (name : String) (cases : List (Nat × Case)) :
    IO System.FilePath := do
  let d := dir / name
  IO.FS.createDirAll d
  IO.FS.writeFile (d / "main.sol") (solContract s!"abidiff_{name}" cases)
  IO.FS.writeFile (d / "calls") (callsFile cases)
  return d / "main.sol"

/-- One line of the runner's output. -/
structure CallResult where
  status : String
  returndata : String
  message : String := ""

def parseResults (s : String) : Except String (List CallResult) :=
  ((s.splitOn "\n").filter (!·.trimAscii.isEmpty)).mapM fun line => do
    let j ← Json.parse line
    return { status := ← j.getObjValAs? String "status"
             returndata := ← j.getObjValAs? String "returndata"
             message := (j.getObjValAs? String "message").toOption.getD "" }

/-- Compare one call's result with the model's prediction. -/
def judge (check : Check) (call : Call) (r : CallResult) : Outcome :=
  if r.status != "success" then
    .diverge check "failure" s!"reverted with `0x{r.returndata}` ({r.message})"
  else if r.returndata.toLower == call.returndata then .agree
  else .diverge check r.returndata "returned other bytes than the model predicts"

/-- The outcome of case `i` from the results of its calls (`Case.calls`): the
    first divergence, encoder first. -/
def judgeCase (i : Nat) (c : Case) (rs : List CallResult) : Outcome :=
  let checks := (c.calls i).zip ([Check.encode, Check.echo].zip rs)
  match checks.map (fun (call, k, r) => judge k call r) |>.find? (!·.isAgree) with
  | some o => o
  | none => .agree

/-- Compile and run one batch. `.error` carries the compiler's diagnostics. -/
def runOnce (ctx : Ctx) (cases : List (Nat × Case)) : IO (Except String (List Outcome)) := do
  let k ← ctx.counter.modifyGet fun n => (n, n + 1)
  let src ← writeBatch ctx.dir s!"batch{k}" cases
  let d := ctx.dir / s!"batch{k}"
  let output := d / "out.jsonl"
  let out ← IO.Process.output
    { cmd := "scripts/run-solcore-rs.sh"
      args := #[src.toString, (d / "calls").toString, output.toString]
      env := #[("ABIDIFF_RPC", some ctx.rpc)] }
  if out.exitCode == 3 then return .error out.stderr
  if out.exitCode == 5 then
    return .ok (cases.map fun _ =>
      .diverge .encode "failure" s!"deployment failed: {out.stderr.trimAscii}")
  if out.exitCode != 0 then
    throw <| IO.userError s!"run-solcore-rs.sh failed with code {out.exitCode}:\n{out.stderr}"
  match parseResults (← IO.FS.readFile output) with
  | .error e => throw <| IO.userError s!"cannot read {output}: {e}"
  | .ok rs =>
    let n := (cases.map fun (i, c) => (c.calls i).length).sum
    if rs.length != n then
      throw <| IO.userError s!"{output}: expected {n} results, got {rs.length}"
    let (os, _) := cases.foldl (init := (#[], rs)) fun (os, rs) (i, c) =>
      let k := (c.calls i).length
      (os.push (judgeCase i c (rs.take k)), rs.drop k)
    return .ok os.toList

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
