/-
CLI for the direct native emitter. See Native/ELF.lean for the exact
supported target and verification/ABI boundaries.
-/
import Lean4LeanCompiler.Native.ELF

def main (args : List String) : IO UInt32 := do
  match args with
  | [file] =>
    if !Lean4LeanCompiler.Native.ELF.layoutValid then
      IO.eprintln "internal native ELF layout check failed"
      return 1
    IO.FS.writeBinFile (System.FilePath.mk file)
      (Lean4LeanCompiler.Native.ELF.compile Lean4LeanCompiler.Native.registered)
    IO.println s!"direct-native: emitted {Lean4LeanCompiler.Native.ELF.objectBytes.length} ELF64/x86-64 bytes to {file}"
    IO.println "symbols: l4lc_add64 (SysV u64,u64->u64), l4lc_copy4 (SysV pointer,pointer->void)"
    IO.println "source proof: Lean kernel; instruction proof: modeled x86 subset; CPU/ELF loader not verified"
    return 0
  | _ =>
    IO.eprintln "usage: lake exe lean4leanNative PATH_TO_OBJECT.o"
    return 2
