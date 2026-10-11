/-
Independent executable validator written in Lean 4: reads a produced ELF file
and accepts only exact byte equality with the compilation of the
Lean-extracted, source-proof-checked register selection.
-/
import Lean4LeanCompiler.Native.SourceLink
import Lean4LeanCompiler.Native.ELFScalar

open Lean4LeanCompiler.Native

def main (args : List String) : IO UInt32 := do
  match args with
  | [path] =>
    let bytes ← IO.FS.readBinFile (System.FilePath.mk path)
    let r := Lean4LeanCompiler.NativeExamples.extractedScalar
    if ELFScalar.checkObject r bytes then
      IO.println "PASS: exact output object validated against theorem-bound LCNF selection"
      return 0
    else
      IO.eprintln "REJECT: artifact differs from source-bound native object"
      return 1
  | _ =>
    IO.eprintln "usage: lake exe lean4leanCheckNative FILE.o"
    return 2
