/-
Exact-byte validator bound to the compiler-generated selection for either
ordinary Lean source declaration. Reject wrong function and corrupted bytes.
-/
import Lean4LeanCompiler.Native.SourceLink
import Lean4LeanCompiler.Native.ELFScalar

open Lean4LeanCompiler.Native

def checkOne (which path : String) : IO UInt32 := do
  let r? := match which with
    | "returnScalar" => some Lean4LeanCompiler.NativeExamples.extractedScalar
    | "returnSecond" => some Lean4LeanCompiler.NativeExamples.extractedSecond
    | _ => none
  let some r := r?
    | IO.eprintln "REJECT: unsupported source function"
      return 2
  let bytes ← IO.FS.readBinFile (System.FilePath.mk path)
  if ELFScalar.checkObject r bytes then
    IO.println s!"PASS: exact native ELF bytes matched source-bound {which}"
    return 0
  else
    IO.eprintln s!"REJECT: native ELF bytes differ from checked {which} output"
    return 1

def main (args : List String) : IO UInt32 := do
  match args with
  | [path] => checkOne "returnScalar" path
  | [which, path] => checkOne which path
  | _ =>
    IO.eprintln "usage: lake exe lean4leanCheckNative [returnScalar|returnSecond] FILE.o"
    return 2
