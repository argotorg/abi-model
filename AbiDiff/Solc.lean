import Lean.Data.Json
import AbiModel.EncodeAnn
import AbiModel.FFI.Keccak

/-!
Rendering model cases as Solcore source and as the test runner's hex strings.

A `Case` is a type of the model together with a value of it. Its Solcore source
is produced from the same `Ty`/`Value` the model encodes, with an explicit type
annotation, so every generated method is well typed by construction as long as
the type is `supported` (i.e. the std library has the ABI instances for it).
-/

namespace AbiDiff
open AbiModel

structure Case where
  t : Ty
  v : Value t

/-! ## Hex -/

def hexPad (width n : Nat) : String :=
  let s := String.ofList (Nat.toDigits 16 n)
  String.ofList (List.replicate (width - s.length) '0') ++ s

def hexWord (w : Word) : String := hexPad 64 w.toNat

/-- The words of a `memory<bytes>` return value: `[0x20][len][payload]`. -/
def returnWords (payload : Wire) : Wire :=
  natW 0x20 :: natW (32 * payload.length) :: payload

def hexWire (w : Wire) : String := String.join (w.map hexWord)

/-- Split runner hex output into 32-byte words (a short last word is right-padded). -/
def hexToWords (s : String) : List Nat :=
  let digits := s.toList
  let rec go (fuel : Nat) (cs : List Char) : List Nat :=
    match fuel, cs with
    | 0, _ | _, [] => []
    | fuel + 1, cs =>
      let w := cs.take 64
      let w := w ++ List.replicate (64 - w.length) '0'
      let n := w.foldl (fun acc c =>
        acc * 16 + (if c.isDigit then c.toNat - '0'.toNat
                    else if 'a' ≤ c ∧ c ≤ 'f' then c.toNat - 'a'.toNat + 10
                    else if 'A' ≤ c ∧ c ≤ 'F' then c.toNat - 'A'.toNat + 10 else 0)) 0
      n :: go fuel (cs.drop 64)
  go digits.length digits

/-! ## Types and values -/

/-- The Solcore type of a model type, when the std can `abi_encode` it from memory. -/
def solTy : Ty → Option String
  | .unit => some "()"
  | .word => some "uint256"
  | .bool => some "bool"
  | .pair a b => do pure s!"({← solTy a}, {← solTy b})"
  | .sum a b => do pure s!"sum<{← solTy a}, {← solTy b}>"
  | .tup a => do pure s!"ABITuple<{← solTy a}>"
  -- `ABIEncode<memory<DynArray<t>>>` requires `t : Typedef<word>` (std.sol)
  | .array .word => some "memory<DynArray<uint256>>"
  | .array _ => none

def supported (t : Ty) : Bool := (solTy t).isSome

def solExpr : (t : Ty) → Value t → String
  | .unit, _ => "()"
  | .word, w => toString w.toNat
  | .bool, b => if b then "true" else "false"
  | .pair a b, v => s!"({solExpr a v.1}, {solExpr b v.2})"
  | .sum a _, .inl x => s!"inl({solExpr a x})"
  | .sum _ b, .inr y => s!"inr({solExpr b y})"
  | .tup a, x => s!"ABITuple({solExpr a x})"
  | .array a, xs => "[" ++ ", ".intercalate (xs.attach.map fun ⟨x, _⟩ => solExpr a x) ++ "]"

/-- Compact, readable rendering of a model type. -/
def showTy : Ty → String
  | .unit => "unit"
  | .word => "word"
  | .bool => "bool"
  | .pair a b => s!"pair {showArg a} {showArg b}"
  | .sum a b => s!"sum {showArg a} {showArg b}"
  | .tup a => s!"tup {showArg a}"
  | .array a => s!"array {showArg a}"
where
  showArg : Ty → String
    | .unit => "unit" | .word => "word" | .bool => "bool"
    | t => "(" ++ showTy t ++ ")"

def showWord (w : Word) : String :=
  if w.toNat < 2 ^ 32 then toString w.toNat else "0x" ++ String.ofList (Nat.toDigits 16 w.toNat)

def showVal : (t : Ty) → Value t → String
  | .unit, _ => "()"
  | .word, w => showWord w
  | .bool, b => toString b
  | .pair a b, v => s!"({showVal a v.1}, {showVal b v.2})"
  | .sum a _, .inl x => s!"inl {showVal a x}"
  | .sum _ b, .inr y => s!"inr {showVal b y}"
  | .tup a, x => s!"tup {showVal a x}"
  | .array a, xs => "[" ++ ", ".intercalate (xs.attach.map fun ⟨x, _⟩ => showVal a x) ++ "]"

def Case.describe (c : Case) : String := s!"{showTy c.t} = {showVal c.t c.v}"

/-- Model prediction for the call's return data, labelled by role. -/
def Case.expected (c : Case) : List (String × Word) :=
  ("bytes offset", natW 0x20) :: ("bytes length", natW (32 * (encodeBytes c.t c.v).length)) ::
    (encodeAnn 32 c.t c.v).map fun cell => (cell.role.name, cell.val)

def Case.expectedHex (c : Case) : String := hexWire (returnWords (encodeBytes c.t c.v))

/-- Feature tags, for the per-area summary. -/
def tags : Ty → List String
  | .unit | .word | .bool => []
  | .pair a b => tags a ++ tags b
  | .sum a b => "sums" :: tags a ++ tags b
  | .tup a => "ABITuple" :: tags a
  | .array a => "arrays" :: tags a

def Case.areas (c : Case) : List String :=
  let ts := (tags c.t).eraseDups
  let ts := if isStatic c.t then "static" :: ts else "dynamic" :: ts
  ts

/-! ## Contract and test file -/

def methodName (i : Nat) : String := s!"case{i}"

def selectorHex (i : Nat) : String := hexPad 8 (FFI.selector s!"{methodName i}()").toNat

def solMethod (i : Nat) (c : Case) : String :=
  let ty := (solTy c.t).getD "<unsupported>"
  s!"  // {c.describe}
  function {methodName i}() public returns (memory<bytes>) \{
    let v : {ty} = {solExpr c.t c.v};
    return abi_encode(v);
  }
"

def header : String :=
"import * from std;
import * from std.dispatch;
import * from std.Generic;
import * from std.ABIGeneric;
pragma no-patterson-condition ;
pragma no-coverage-condition ;
pragma no-bounded-variable-condition ;

// Generated by abi-model (`lake exe abidiff`). Do not edit.
"

/-- Source of a contract with one method per case, numbered by `ids`. -/
def solContract (cases : List (Nat × Case)) : String :=
  header ++ "\ncontract AbiModelDiff {\n  constructor() {}\n\n" ++
    "\n".intercalate (cases.map fun (i, c) => solMethod i c) ++ "}\n"

def jsonString (s : String) : String := Lean.Json.compress (Lean.Json.str s)

/-- The test file in the format of solcore's `test/examples/dispatch/*.json`. -/
def testJson (suite : String) (cases : List (Nat × Case)) : String :=
  let ctor := "      { \"kind\": \"constructor\", \"input\": { \"comment\": \"constructor()\", \"calldata\": \"\", \"value\": \"0\" } }"
  let call (i : Nat) (c : Case) :=
    s!"      \{ \"kind\": \"call\",
        \"input\": \{ \"comment\": {jsonString s!"{methodName i}: {c.describe}"}, \"calldata\": \"{selectorHex i}\", \"value\": \"0\" },
        \"output\": \{ \"status\": \"success\", \"returndata\": \"{c.expectedHex}\" } }"
  s!"\{
  \"{suite}\": \{
    \"bytecode\": \"\",
    \"contract\": \"AbiModelDiff\",
    \"tests\": [
" ++ ",\n".intercalate (ctor :: cases.map fun (i, c) => call i c) ++ "
    ]
  }
}
"

end AbiDiff
