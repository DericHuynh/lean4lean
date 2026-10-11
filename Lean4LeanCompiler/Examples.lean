/-
Compiled ordinary Lean examples; no toy AST fixtures. The new experimental
LCNF pass applies ONLY in the Examples namespace. Results are compared with
an independently stock-compiled reference module.
-/
import Lean4LeanCompiler.Reference
import Lean4LeanCompiler.LCNFExperimental
import Lean4LeanCompiler.LCNFAudit

namespace Lean4LeanCompiler.Examples

def copyFour (src : ByteArray) : ByteArray := Id.run do
  if src.size < 4 then return ByteArray.empty
  let mut dst := ByteArray.emptyWithCapacity 4
  dst := dst.push (src.get! 0)
  dst := dst.push (src.get! 1)
  dst := dst.push (src.get! 2)
  dst := dst.push (src.get! 3)
  return dst

def reverseFour (src : ByteArray) : ByteArray := Id.run do
  if src.size != 4 then return src
  let a := src.get! 0
  let b := src.get! 1
  let c := src.get! 2
  let d := src.get! 3
  let mut dst := src
  dst := dst.set! 0 d
  dst := dst.set! 1 c
  dst := dst.set! 2 b
  dst := dst.set! 3 a
  return dst

def writeFourInto (src dst : ByteArray) : Option ByteArray := Id.run do
  if src.size < 4 then return none
  if dst.size != 4 then return none
  let a := src.get! 0
  let b := src.get! 1
  let c := src.get! 2
  let d := src.get! 3
  let mut out := dst
  out := out.set! 0 a
  out := out.set! 1 b
  out := out.set! 2 c
  out := out.set! 3 d
  return some out

def bumpList (xs : List UInt8) : List UInt8 :=
  xs.map (· + 1)

/-- Tests actual Lean ByteArray behavior; NOT physical allocation counts. -/
def smokeTest : IO Unit := do
  let source := ([11, 22, 33, 44] : List UInt8).toByteArray
  let copied := copyFour source
  unless copied.size == 4 && copied.get! 0 == 11 && copied.get! 3 == 44 do
    throw <| IO.userError "copyFour mismatch"
  let saved := source
  let reversed := reverseFour source
  unless saved.get! 0 == 11 && reversed.get! 0 == 44 && reversed.get! 3 == 11 do
    throw <| IO.userError "reverseFour changed shared input"
  let target := ([0, 0, 0, 0] : List UInt8).toByteArray
  let some written := writeFourInto source target
    | throw <| IO.userError "writeFourInto rejected valid destination"
  unless written == source do
    throw <| IO.userError "writeFourInto mismatch"
  unless (writeFourInto source ByteArray.empty).isNone do
    throw <| IO.userError "accepted insufficient destination capacity"
  unless (writeFourInto ByteArray.empty target).isNone do
    throw <| IO.userError "accepted insufficient input"
  for n in [0, 1, 2, 3, 4, 5, 7, 12] do
    let input := ((List.range n).map (fun i => (i * 23 + 7).toUInt8)).toByteArray
    unless copyFour input == Lean4LeanCompiler.Reference.copyFour input do
      throw <| IO.userError s!"copyFour vs stock mismatch at length {n}"
    unless reverseFour input == Lean4LeanCompiler.Reference.reverseFour input do
      throw <| IO.userError s!"reverseFour vs stock mismatch at length {n}"
    unless writeFourInto input target == Lean4LeanCompiler.Reference.writeFourInto input target do
      throw <| IO.userError s!"writeFourInto vs stock mismatch at length {n}"
  unless bumpList [0, 1, 255] == Lean4LeanCompiler.Reference.bumpList [0, 1, 255] do
    throw <| IO.userError "bumpList vs stock mismatch"
  IO.println "Lean compiled differential tests passed; resource certification=false"

end Lean4LeanCompiler.Examples

def main : IO Unit := Lean4LeanCompiler.Examples.smokeTest
