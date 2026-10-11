/-
Read a persisted extraction from compilation of actual ordinary Lean code.
Fail closed for missing or ambiguous compiled declarations. This executable
writes ELF machine code bytes in Lean 4 without an intermediate assembler.
-/
import Lean4LeanCompiler.Native.ELFScalar

open Lean
open Lean4LeanCompiler.Native

unsafe def main (args : List String) : IO UInt32 := do
  match args with
  | [path] =>
    Lean.initSearchPath (← Lean.findSysroot)
    let env ← Lean.importModules
      #[{module := Name.str (Name.mkSimple "Lean4LeanCompiler") "NativeExamples"}] {} 0
    let entries := FromLCNF.exportedNative.getState env
    let selected := entries.toList.filter fun e =>
      e.name.toString == "Lean4LeanCompiler.NativeExamples.returnScalar"
    match selected with
    | [entry] =>
      if !ELFScalar.layoutValid entry.arg then
        IO.eprintln "native-from-lcnf: internal layout failure"
        return 1
      IO.FS.writeBinFile (System.FilePath.mk path) (ELFScalar.compile entry)
      IO.println s!"native-from-lcnf: compiled {entry.name} from persisted impure LCNF"
      IO.println s!"ELF64 x86-64 SysV symbol={ELFScalar.symbolName}, bytes={(ELFScalar.objectBytes entry.arg).length}, fallback=false"
      IO.println "certification: checked scalar shape; modeled register semantics; physical ABI and erasure not proved"
      return 0
    | [] =>
      IO.eprintln "native-from-lcnf: no checked extraction entry; no fallback/object"
      return 2
    | _ =>
      IO.eprintln "native-from-lcnf: stale/ambiguous extraction entries"
      return 3
  | _ =>
    IO.eprintln "usage: lake exe lean4leanFromLCNF FILE.o"
    return 4
