/-
Emit an ELF64/x86-64 relocatable object from the register chosen by the
actual impure-LCNF compiler pass. This separate backend is intentionally
restricted to a direct scalar return. No C/LLVM/assembler intermediate.
-/
import Lean4LeanCompiler.Native.ELF
import Lean4LeanCompiler.Native.FromLCNF

namespace Lean4LeanCompiler.Native.ELFScalar
open Lean4LeanCompiler.Native

def symbolName : String := "l4lc_from_lcnf"

def sectionNames : List UInt8 :=
  [0] ++ ELF.zstr ".text" ++ ELF.zstr ".symtab" ++
  ELF.zstr ".strtab" ++ ELF.zstr ".shstrtab"

def symbolNames : List UInt8 := [0] ++ ELF.zstr symbolName

def textBytes (r : FromLCNF.Register) : List UInt8 := FromLCNF.encode r

def symbolTable (r : FromLCNF.Register) : List UInt8 :=
  ELF.symbol 0 0 0 0 0 ++
  ELF.symbol 0 3 1 0 0 ++
  ELF.symbol 1 0x12 1 0 (textBytes r).length

def textOffset : Nat := 64
def symbolsOffset (r : FromLCNF.Register) : Nat :=
  ELF.alignUp (textOffset + (textBytes r).length) 8
def stringsOffset (r : FromLCNF.Register) : Nat :=
  symbolsOffset r + (symbolTable r).length
def namesOffset (r : FromLCNF.Register) : Nat :=
  stringsOffset r + symbolNames.length
def headersOffset (r : FromLCNF.Register) : Nat :=
  ELF.alignUp (namesOffset r + sectionNames.length) 8

def fileHeader (r : FromLCNF.Register) : List UInt8 :=
  [127, 69, 76, 70, 2, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0] ++
  ELF.le 1 2 ++ ELF.le 62 2 ++ ELF.le 1 4 ++
  ELF.le 0 8 ++ ELF.le 0 8 ++ ELF.le (headersOffset r) 8 ++
  ELF.le 0 4 ++ ELF.le 64 2 ++ ELF.le 0 2 ++ ELF.le 0 2 ++
  ELF.le 64 2 ++ ELF.le 5 2 ++ ELF.le 4 2

def sectionHeaders (r : FromLCNF.Register) : List UInt8 :=
  List.replicate 64 0 ++
  ELF.sectionHeader 1 1 6 textOffset (textBytes r).length 0 0 1 0 ++
  ELF.sectionHeader 7 2 0 (symbolsOffset r) (symbolTable r).length 3 2 8 24 ++
  ELF.sectionHeader 15 3 0 (stringsOffset r) symbolNames.length 0 0 1 0 ++
  ELF.sectionHeader 23 3 0 (namesOffset r) sectionNames.length 0 0 1 0

def objectBytes (r : FromLCNF.Register) : List UInt8 :=
  fileHeader r ++ textBytes r ++
  ELF.padTo (textOffset + (textBytes r).length) (symbolsOffset r) ++
  symbolTable r ++ symbolNames ++ sectionNames ++
  ELF.padTo (namesOffset r + sectionNames.length) (headersOffset r) ++
  sectionHeaders r

def compile (entry : FromLCNF.Entry) : ByteArray :=
  (objectBytes entry.arg).toByteArray

def layoutValid (r : FromLCNF.Register) : Bool :=
  (fileHeader r).length == 64 &&
  (sectionHeaders r).length == 5 * 64 &&
  (symbolTable r).length == 3 * 24 &&
  (symbolsOffset r) % 8 == 0 &&
  (headersOffset r) % 8 == 0 &&
  (objectBytes r).length == headersOffset r + 5 * 64 &&
  (textBytes r).length == 4

set_option maxRecDepth 16384 in
theorem layout_valid (r : FromLCNF.Register) : layoutValid r = true := by
  cases r <;> decide

set_option maxRecDepth 16384 in
theorem emitted_text_decodes (r : FromLCNF.Register) :
    FromLCNF.decode
      (((objectBytes r).drop textOffset).take (textBytes r).length) =
      some r := by
  cases r <;> decide

set_option maxRecDepth 16384 in
theorem emitted_magic (r : FromLCNF.Register) :
    (objectBytes r).take 4 = [127, 69, 76, 70] := by
  cases r <;> decide

end Lean4LeanCompiler.Native.ELFScalar
