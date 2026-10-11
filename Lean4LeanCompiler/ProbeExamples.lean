import Lean4LeanCompiler.ProbeAppend

namespace Lean4LeanCompiler.ProbeExamples

def triple (a b c : ByteArray) : ByteArray := (a.fastAppend b).fastAppend c

def tripleAppend (a b c : ByteArray) : ByteArray := (a ++ b) ++ c

def mainTest : IO Unit := do
  let a := ([1, 2] : List UInt8).toByteArray
  let b := ([3] : List UInt8).toByteArray
  let c := ([4, 5] : List UInt8).toByteArray
  unless triple a b c == ([1, 2, 3, 4, 5] : List UInt8).toByteArray do
    throw <| IO.userError "probe mismatch"
  unless tripleAppend a b c == triple a b c do
    throw <| IO.userError "append mismatch"
  IO.println "append probe compiled and ran"

end Lean4LeanCompiler.ProbeExamples

def main : IO Unit := Lean4LeanCompiler.ProbeExamples.mainTest
