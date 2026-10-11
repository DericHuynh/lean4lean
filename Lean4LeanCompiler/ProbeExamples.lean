import Lean4LeanCompiler.ProbeAppend
import Lean4LeanCompiler.AppendFusionPilot

namespace Lean4LeanCompiler.ProbeExamples

def triple (a b c : ByteArray) : ByteArray := (a.fastAppend b).fastAppend c

def tripleAppend (a b c : ByteArray) : ByteArray := (a ++ b) ++ c

def duplicateIntermediate (a b : ByteArray) : ByteArray :=
  let prefix := a ++ b
  prefix ++ prefix

def mainTest : IO Unit := do
  let a := ([1, 2] : List UInt8).toByteArray
  let b := ([3] : List UInt8).toByteArray
  let c := ([4, 5] : List UInt8).toByteArray
  unless triple a b c == ([1, 2, 3, 4, 5] : List UInt8).toByteArray do
    throw <| IO.userError "probe mismatch"
  unless tripleAppend a b c == triple a b c do
    throw <| IO.userError "append mismatch"
  let prefix := a.fastAppend b
  unless duplicateIntermediate a b == prefix.fastAppend prefix do
    throw <| IO.userError "double-use intermediate unexpectedly fused"
  IO.println "append probe compiled and ran"

end Lean4LeanCompiler.ProbeExamples

def main : IO Unit := Lean4LeanCompiler.ProbeExamples.mainTest
