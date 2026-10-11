/-
One native ELF object per checked ordinary Lean declaration. Both selections
come from actual compiler-generated constants and both must pass source
equality theorems in the imported SourceLink module.
-/
import Lean4LeanCompiler.Native.SourceLink
import Lean4LeanCompiler.Native.ELFScalar

open Lean4LeanCompiler.Native

def entryFor? (name : String) : Option FromLCNF.Entry :=
  match name with
  | "returnScalar" =>
    some { name := Lean.Name.str (Lean.Name.str (Lean.Name.mkSimple "Lean4LeanCompiler") "NativeExamples") "returnScalar"
           arg := Lean4LeanCompiler.NativeExamples.extractedScalar }
  | "returnSecond" =>
    some { name := Lean.Name.str (Lean.Name.str (Lean.Name.mkSimple "Lean4LeanCompiler") "NativeExamples") "returnSecond"
           arg := Lean4LeanCompiler.NativeExamples.extractedSecond }
  | _ => none

def generateOne (which path : String) : IO UInt32 := do
  let some entry := entryFor? which
    | IO.eprintln "native-from-lcnf: unsupported entry point; no fallback"
      return 2
  if !ELFScalar.layoutValid entry.arg then
    IO.eprintln "native-from-lcnf: invalid checked ELF layout"
    return 1
  IO.FS.writeBinFile (System.FilePath.mk path) (ELFScalar.compile entry)
  IO.println s!"native-from-lcnf: {entry.name}; register={repr entry.arg}; fallback=false"
  IO.println s!"ELF64 x86-64 symbol={ELFScalar.symbolName}, bytes={(ELFScalar.objectBytes entry.arg).length}"
  IO.println "source/register relation kernel checked; physical CPU/ABI and erasure unproved"
  return 0

def main (args : List String) : IO UInt32 := do
  match args with
  | [path] => generateOne "returnScalar" path
  | [which, path] => generateOne which path
  | _ =>
    IO.eprintln "usage: lake exe lean4leanFromLCNF [returnScalar|returnSecond] FILE.o"
    return 2
