/-
The untrusted actual-LCNF extractor emits a plain Lean constant while
compiling NativeExamples. Native.SourceLink proves the source equality
for that exact selection before this native executable can be built.
-/
import Lean4LeanCompiler.Native.SourceLink
import Lean4LeanCompiler.Native.ELFScalar

open Lean4LeanCompiler.Native

def main (args : List String) : IO UInt32 := do
  match args with
  | [path] =>
    let entry : FromLCNF.Entry :=
      { name := Lean.Name.str (Lean.Name.str (Lean.Name.mkSimple "Lean4LeanCompiler") "NativeExamples") "returnScalar"
        arg := Lean4LeanCompiler.NativeExamples.extractedScalar }
    if !ELFScalar.layoutValid entry.arg then
      IO.eprintln "native-from-lcnf: invalid checked ELF layout"
      return 1
    IO.FS.writeBinFile (System.FilePath.mk path) (ELFScalar.compile entry)
    IO.println s!"native-from-lcnf: {entry.name}; register={repr entry.arg}; fallback=false"
    IO.println s!"ELF64 x86-64 symbol={ELFScalar.symbolName}, bytes={(ELFScalar.objectBytes entry.arg).length}"
    IO.println "source/register relation kernel checked; physical CPU/ABI and erasure unproved"
    return 0
  | _ =>
    IO.eprintln "usage: lake exe lean4leanFromLCNF FILE.o"
    return 2
