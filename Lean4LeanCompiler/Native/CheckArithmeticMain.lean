/-
Executable exact-artifact validator: must match all bytes of the ELF object
for the compiler-generated source-verified actual-LCNF selected operation.
-/
import Lean4LeanCompiler.Native.ELFArithmetic

open Lean4LeanCompiler.Native

def main (args : List String) : IO UInt32 := do
  match args with
  | [path] =>
    let bytes ← IO.FS.readBinFile (System.FilePath.mk path)
    let op := Lean4LeanCompiler.NativeArithmeticExamples.extractedAddition
    if ELFArithmetic.checkObject op bytes then
      IO.println "PASS: arithmetic ELF file matches exact theorem-bound output"
      return 0
    else
      IO.eprintln "REJECT: arithmetic ELF file differs from theorem-bound output"
      return 1
  | _ =>
    IO.eprintln "usage: lake exe lean4leanCheckAddNative OBJECT.o"
    return 2
