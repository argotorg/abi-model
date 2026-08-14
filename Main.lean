import AbiModel
import Plausible

open Plausible AbiModel

def testConfig : Configuration :=
  { numInst := 1000, maxSize := 20, quiet := true }

def runCheck (name : String) (p : Prop) [Testable p] : IO Bool := do
  match ← Testable.checkIO p testConfig with
  | .success _ =>
    IO.println s!"ok      {name}"
    return true
  | .gaveUp n =>
    IO.println s!"gaveup  {name} ({n} discarded)"
    return false
  | .failure _ xs _ =>
    IO.println s!"FAIL    {name}"
    for x in xs do
      IO.println s!"        {x}"
    return false

def main : IO UInt32 := do
  let mut rs : List Bool := []
  rs := List.concat rs (← runCheck "generator produces well formed values"
    (NamedBinder "s" (∀ s : Sample, propWellTyped s = true)))
  rs := List.concat rs (← runCheck "decode (encode v) = ok v"
    (NamedBinder "s" (∀ s : Sample, propRoundTrip s = true)))
  rs := List.concat rs (← runCheck "re-encoding the decoded value yields the same wire"
    (NamedBinder "s" (∀ s : Sample, propEncodeStable s = true)))
  rs := List.concat rs (← runCheck "wire is a multiple of 32 and at least headSize"
    (NamedBinder "s" (∀ s : Sample, propWireShape s = true)))
  rs := List.concat rs (← runCheck "sum body fits in the reserved head"
    (NamedBinder "s" (∀ s : Sample, propInnerFits s = true)))
  rs := List.concat rs (← runCheck "variant tags are pairwise distinct"
    (NamedBinder "i" (∀ i : Nat, NamedBinder "j" (∀ j : Nat, propTagsDistinct i j = true))))
  rs := List.concat rs (← runCheck "static tup round trips"
    (NamedBinder "s" (∀ s : Sample, propTupStatic s = true)))
  rs := List.concat rs (← runCheck "dynamic tup in first position round trips"
    (NamedBinder "s" (∀ s : Sample, propTupDynFirst s = true)))
  rs := List.concat rs (← runCheck "arbitrary tag is not rejected, falls through to the last variant"
    (NamedBinder "n" (∀ n : Nat, propTagLenient n = true)))
  rs := List.concat rs (← runCheck "dirty static sum padding is ignored"
    (NamedBinder "n" (∀ n : Nat, propPadIgnored n = true)))
  rs := List.concat rs (← runCheck "trailing garbage is ignored"
    (NamedBinder "s" (∀ s : Sample, NamedBinder "n" (∀ n : Nat, propTrailingIgnored s n = true))))
  rs := List.concat rs (← runCheck "truncated wire does not fail, reads zeros"
    (NamedBinder "s" (∀ s : Sample, propTruncationZeros s = true)))
  rs := List.concat rs (← runCheck "dirty higher bits of bytes4 survive decoding"
    (NamedBinder "n" (∀ n : Nat, propDirtyB4 n = true)))
  rs := List.concat rs (← runCheck "dirty bool is rejected"
    (NamedBinder "n" (∀ n : Nat, propDirtyBoolRejected n = true)))
  rs := List.concat rs (← runCheck "dirty address is rejected"
    (NamedBinder "n" (∀ n : Nat, propDirtyAddrRejected n = true)))
  rs := List.concat rs (← runCheck "non canonical offset is followed"
    (NamedBinder "bs" (∀ bs : List UInt8, propOffsetLenient bs = true)))
  rs := List.concat rs (← runCheck "aliased offsets decode the same tail"
    (NamedBinder "bs" (∀ bs : List UInt8, propAliasing bs = true)))
  rs := List.concat rs (← runCheck "decode is not injective"
    (NamedBinder "bs" (∀ bs : List UInt8, propNonInjective bs = true)))
  rs := List.concat rs (← runCheck "inflated array length reads zeroed elements"
    (NamedBinder "n" (∀ n : Nat, propArrayLenient n = true)))
  rs := List.concat rs (← runCheck "dynamic tup outside first position breaks the round trip"
    (propTupDynQuirk = true))
  if List.all rs id then
    IO.println s!"{List.length rs} properties passed"
    return 0
  else
    IO.println s!"{List.countP (fun b => b == false) rs} of {List.length rs} properties failed"
    return 1
