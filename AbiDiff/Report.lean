import AbiDiff.Runner

/-! The Markdown report of a differential run. -/

namespace AbiDiff
open AbiModel

structure Meta where
  solcore : String
  abiModel : String
  mode : String
  date : String
  solc : String

structure Result where
  id : Nat
  case : Case
  outcome : Outcome
  /-- Smallest diverging case found by shrinking, its outcome, and the steps taken. -/
  shrunk : Option (Case × Outcome × Nat) := none
  regression : Option String := none

def shortHex (n : Nat) : String := "0x" ++ String.ofList (Nat.toDigits 16 n)

/-- Word-by-word comparison; long runs of equal words are collapsed. -/
def wordTable (c : Case) (actualHex : String) : String := Id.run do
  let exp := c.expected
  let act := hexToWords actualHex
  let n := max exp.length act.length
  let row (i : Nat) : Bool × String :=
    let e := exp[i]?.map (·.2.toNat)
    let a := act[i]?
    let role := (exp[i]?.map (·.1)).getD "—"
    let same := e == a
    let show_ := fun (x : Option Nat) => x.elim "—" fun v => "`" ++ shortHex v ++ "`"
    (same, s!"| {i} | {show_ e} | {show_ a} | {role} | {if same then "" else "✗"} |")
  let rows := (List.range n).map row
  let keep (i : Nat) : Bool :=
    !(rows[i]!.1) || i == 0 || i + 1 == n ||
      (i > 0 && !(rows[i - 1]!.1)) || (i + 1 < n && !(rows[i + 1]!.1))
  let mut out := "| # | expected (model) | actual (solcore) | role | |\n|---|---|---|---|---|\n"
  let mut skipped := false
  for i in List.range n do
    if keep i then
      out := out ++ rows[i]!.2 ++ "\n"
      skipped := false
    else if !skipped then
      out := out ++ "| … | | | | |\n"
      skipped := true
  return out

def caseBlock (id : Nat) (c : Case) (o : Outcome) : String :=
  let src := s!"```solidity\n{(solMethod id c).trimAsciiEnd.toString}\n```\n"
  match o with
  | .diverge "failure" msg => src ++ s!"\nThe call **reverted** ({msg}).\n"
  | .diverge actual msg =>
      src ++ s!"\n{msg}\n\n" ++ wordTable c actual
  | .compileFail err =>
      let lines := (err.splitOn "\n").filter (!·.trimAscii.isEmpty) |>.take 12
      src ++ "\n```\n" ++ "\n".intercalate lines ++ "\n```\n"
  | .agree => src

def areas : List String := ["static", "dynamic", "arrays", "sums", "ABITuple"]

def report (m : Meta) (rs : List Result) : String := Id.run do
  let agree := rs.filter (·.outcome.isAgree)
  let diverge := rs.filter (·.outcome.isDiverge)
  let failed := rs.filter fun r => !r.outcome.isAgree && !r.outcome.isDiverge
  let mut s := "# abi-model × Solcore: differential report\n\n"
  s := s ++ "| | |\n|---|---|\n"
  s := s ++ s!"| Solcore | `{m.solcore}` |\n| abi-model | `{m.abiModel}` |\n"
  s := s ++ s!"| Mode | {m.mode} |\n| Date | {m.date} |\n| solc | {m.solc} |\n\n"
  s := s ++ "## Summary\n\n| Outcome | Count |\n|---|---|\n"
  s := s ++ s!"| ✅ agree | {agree.length} |\n| ❌ diverge | {diverge.length} |\n"
  s := s ++ s!"| ⚠️ compile-fail | {failed.length} |\n\n"
  s := s ++ "| Area | agree / total |\n|---|---|\n"
  for a in areas do
    let inA := rs.filter (·.case.areas.contains a)
    if !inA.isEmpty then
      let ok := inA.filter (·.outcome.isAgree)
      s := s ++ s!"| {a} | {ok.length} / {inA.length} |\n"
  s := s ++ "\n"
  for r in diverge do
    s := s ++ s!"## ❌ case{r.id}: `{showTy r.case.t}`\n\nValue: `{showVal r.case.t r.case.v}`\n\n"
    s := s ++ caseBlock r.id r.case r.outcome
    if let some (c, o, steps) := r.shrunk then
      if steps > 0 then
        s := s ++ s!"\n**Shrunk** in {steps} steps to `{c.describe}`:\n\n" ++ caseBlock 0 c o
    if let some p := r.regression then
      s := s ++ s!"\nRegression test: `{p}`\n"
    s := s ++ "\n"
  if !failed.isEmpty then
    s := s ++ "## ⚠️ Compile failures\n\n"
    for r in failed do
      s := s ++ s!"### case{r.id}: `{r.case.describe}`\n\n" ++ caseBlock r.id r.case r.outcome ++ "\n"
  s := s ++ s!"<details><summary>✅ {agree.length} passing cases</summary>\n\n"
  for r in agree do
    s := s ++ s!"- case{r.id} `{r.case.describe}`\n"
  s := s ++ "\n</details>\n"
  return s

end AbiDiff
