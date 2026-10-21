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

/-!
An enum constructor's fields invert `constrRep` (`DeriveGeneric.hs`): a `unit`
payload is a nullary constructor, a right-nested `pair` is several fields, and
anything else is one field. The tag solcore derives from the declaration is then
the model's `ctorTag`.
-/

mutual

/-- Compact, readable rendering of a model type. -/
def showTy : Ty → String
  | .unit => "unit"
  | .word => "word"
  | .bool => "bool"
  | .pair a b => s!"pair {showArg a} {showArg b}"
  | .sum a b => s!"sum {showArg a} {showArg b}"
  | .tup a => s!"tup {showArg a}"
  | .array a => s!"array {showArg a}"
  | .enum n t cs => "enum {" ++ showCtor n t ++ showCtors cs ++ "}"

def showArg : Ty → String
  | .unit => "unit" | .word => "word" | .bool => "bool"
  | t => "(" ++ showTy t ++ ")"

def showCtor (n : String) (t : Ty) : String := s!"{n} {showArg t}"

def showCtors : Ctors → String
  | .last m u => " | " ++ showCtor m u
  | .cons m u cs => " | " ++ showCtor m u ++ showCtors cs

end

/-- The Solcore name of an enum type. Model enums have no type name, so it is
    derived from the structure: equal enums share one declaration. -/
def enumName (t : Ty) : String := "E_" ++ hexPad 16 (hash (showTy t)).toNat

mutual

/-- Whether an `ABITuple` occurs in a type. -/
def hasTup : Ty → Bool
  | .unit | .word | .bool => false
  | .pair a b | .sum a b => hasTup a || hasTup b
  | .tup _ => true
  | .array a => hasTup a
  | .enum _ t cs => hasTup t || hasTupC cs

def hasTupC : Ctors → Bool
  | .last _ u => hasTup u
  | .cons _ u cs => hasTup u || hasTupC cs

end

mutual

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
  -- the derived `ABIDecode` of an enum needs `ABIDecode<ABITuple<…>>` for an
  -- `ABITuple` field, which no instance provides
  | .enum n t cs => do
      if hasTup t || hasTupC cs then none
      let _ ← solCtor n t
      let _ ← solCtors cs
      pure (enumName (.enum n t cs))
  termination_by t => (sizeOf t, 0)

/-- Field types along a payload's `pair` spine. -/
def solFields : Ty → Option (List String)
  | .pair a b => do pure ((← solTy a) :: (← solFields b))
  | t => do pure [← solTy t]
  termination_by t => (sizeOf t, 1)

/-- A constructor declaration `Name(field, …)`, or `Name` when nullary. -/
def solCtor (n : String) : Ty → Option String
  | .unit => some n
  | t => do pure s!"{n}({", ".intercalate (← solFields t)})"
  termination_by t => (sizeOf t, 2)

def solCtors : Ctors → Option (List String)
  | .last m u => do pure [← solCtor m u]
  | .cons m u cs => do pure ((← solCtor m u) :: (← solCtors cs))
  termination_by cs => (sizeOf cs, 0)

end

def supported (t : Ty) : Bool := (solTy t).isSome

mutual

/-- Declarations of the enums occurring in `t`, nested ones first. -/
def enumDecls : Ty → List String
  | .unit | .word | .bool => []
  | .pair a b | .sum a b => enumDecls a ++ enumDecls b
  | .tup a | .array a => enumDecls a
  | .enum n t cs =>
      let decl := match solCtor n t, solCtors cs with
        | some c, some cs' =>
            [s!"enum {enumName (.enum n t cs)} \{ {", ".intercalate (c :: cs')} }"]
        | _, _ => []
      enumDecls t ++ enumDeclsC cs ++ decl

def enumDeclsC : Ctors → List String
  | .last _ u => enumDecls u
  | .cons _ u cs => enumDecls u ++ enumDeclsC cs

end

mutual

def solExpr : (t : Ty) → Value t → String
  | .unit, _ => "()"
  | .word, w => toString w.toNat
  | .bool, b => if b then "true" else "false"
  | .pair a b, v => s!"({solExpr a v.1}, {solExpr b v.2})"
  | .sum a _, .inl x => s!"inl({solExpr a x})"
  | .sum _ b, .inr y => s!"inr({solExpr b y})"
  | .tup a, x => s!"ABITuple({solExpr a x})"
  | .array a, xs => "[" ++ ", ".intercalate (xs.attach.map fun ⟨x, _⟩ => solExpr a x) ++ "]"
  | .enum n t cs, v => enumName (.enum n t cs) ++ "." ++ armExpr n t cs v
  termination_by t => (sizeOf t, 0)

/-- The selected constructor applied to its fields. -/
def armExpr : (n : String) → (t : Ty) → (cs : Ctors) → Value t ⊕ ValueC cs → String
  | n, t, _, .inl x => ctorExpr n t x
  | _, _, .cons m u cs, .inr y => armExpr m u cs y
  | _, _, .last m u, .inr y => ctorExpr m u y
  termination_by _ t cs => (sizeOf t + sizeOf cs, 0)
  decreasing_by all_goals simp_wf; all_goals first | omega | (have := Ctors.sizeOf_pos ‹Ctors›; omega)

def ctorExpr (n : String) : (t : Ty) → Value t → String
  | .unit, _ => n
  | t, x => n ++ "(" ++ ", ".intercalate (fieldExprs t x) ++ ")"
  termination_by t => (sizeOf t, 2)

/-- Field values along the payload's `pair` spine, as `solFields`. -/
def fieldExprs : (t : Ty) → Value t → List String
  | .pair a b, v => solExpr a v.1 :: fieldExprs b v.2
  | t, x => [solExpr t x]
  termination_by t => (sizeOf t, 1)

end

def showWord (w : Word) : String :=
  if w.toNat < 2 ^ 32 then toString w.toNat else "0x" ++ String.ofList (Nat.toDigits 16 w.toNat)

mutual

def showVal : (t : Ty) → Value t → String
  | .unit, _ => "()"
  | .word, w => showWord w
  | .bool, b => toString b
  | .pair a b, v => s!"({showVal a v.1}, {showVal b v.2})"
  | .sum a _, .inl x => s!"inl {showVal a x}"
  | .sum _ b, .inr y => s!"inr {showVal b y}"
  | .tup a, x => s!"tup {showVal a x}"
  | .array a, xs => "[" ++ ", ".intercalate (xs.attach.map fun ⟨x, _⟩ => showVal a x) ++ "]"
  | .enum n t cs, v => showArm n t cs v
  termination_by t => sizeOf t

/-- The selected constructor and its payload, e.g. `P 9`. -/
def showArm : (n : String) → (t : Ty) → (cs : Ctors) → Value t ⊕ ValueC cs → String
  | n, t, _, .inl x => s!"{n} {showVal t x}"
  | _, _, .cons m u cs, .inr y => showArm m u cs y
  | _, _, .last m u, .inr y => s!"{m} {showVal u y}"
  termination_by _ t cs => sizeOf t + sizeOf cs
  decreasing_by all_goals simp_wf; all_goals first | omega | (have := Ctors.sizeOf_pos ‹Ctors›; omega)

end

def Case.describe (c : Case) : String := s!"{showTy c.t} = {showVal c.t c.v}"

/-- Model prediction for the call's return data, labelled by role. -/
def Case.expected (c : Case) : List (String × Word) :=
  ("bytes offset", natW 0x20) :: ("bytes length", natW (32 * (encodeBytes c.t c.v).length)) ::
    (encodeAnn 32 c.t c.v).map fun cell => (cell.role.name, cell.val)

def Case.expectedHex (c : Case) : String := hexWire (returnWords (encodeBytes c.t c.v))

mutual

/-- Feature tags, for the per-area summary. -/
def tags : Ty → List String
  | .unit | .word | .bool => []
  | .pair a b => tags a ++ tags b
  | .sum a b => "sums" :: tags a ++ tags b
  | .tup a => "ABITuple" :: tags a
  | .array a => "arrays" :: tags a
  | .enum _ t cs => "enums" :: tags t ++ ctorFeatTags cs

def ctorFeatTags : Ctors → List String
  | .last _ u => tags u
  | .cons _ u cs => tags u ++ ctorFeatTags cs

end

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

/-- Source of a contract with one method per case, numbered by `ids`, after the
    declarations of the enums the cases use. -/
def solContract (cases : List (Nat × Case)) : String :=
  let decls := (cases.flatMap fun (_, c) => enumDecls c.t).eraseDups
  header ++ String.join (decls.map (· ++ "\n")) ++
    "\ncontract AbiModelDiff {\n  constructor() {}\n\n" ++
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
