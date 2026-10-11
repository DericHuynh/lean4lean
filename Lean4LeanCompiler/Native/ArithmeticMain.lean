/-
Lean 4 executable emitting real x86-64 ELF bytes for the exactly selected
and source-verified UInt64.add compiler-LCNF operation.
-/
import Lean4LeanCompiler.Native.ELFArithmetic

open Lean4LeanCompiler.Native

def main (args : List String) : IO UInt32 := do
  match args with
  | [path] =>
    let op := Lean4LeanCompiler.NativeArithmeticExamples.extractedAddition
    if !ELFArithmetic.layoutValid op then
      IO.eprintln "native arithmetic: internal ELF layout validation failed"
      return 1
    IO.FS.writeBinFile (System.FilePath.mk path) (ELFArithmetic.compile op)
    IO.println s!"native-arithmetic: actual-LCNF symbol={ELFArithmetic.symbolName}, operation={repr op}, bytes={(ELFArithmetic.objectBytes op).length}, fallback=false"
    IO.println "Lean source result / modeled opcode proven; CPU, linker and erasure not verified"
    return 0
  | _ =>
    IO.eprintln "usage: lake exe lean4leanAddFromLCNF OUTPUT.o"
    return 2
