/-
Direct x86-64 ELF64 ET_REL machine object generation from a typed scalar
operation selected by actual Lean impure-LCNF. C, Rust, LLVM and assembly
are NOT generated intermediate languages. Linker/loader/CPU behavior is a
stated external trust boundary.
-/
import Lean4LeanCompiler.Native.ArithmeticSourceProof
import Lean4LeanCompiler.Native.ELF

namespace Lean4LeanCompiler.Native.ELFArithmetic

open Lean4LeanCompiler.Native

def symbolName : String := "l4lc_add_from_lcnf"

def sectionNames : List UInt8 :=
  [0] ++ ELF.zstr ".text" ++ ELF.zstr ".symtab" ++
  ELF.zstr ".strtab" ++ ELF.zstr ".shstrtab"

def symbolNames : List UInt8 := [0] ++ ELF.zstr symbolName

def textBytes (op : FromLCNFArithmetic.Operation) : List UInt8 :=
  FromLCNFArithmetic.encode op

def symbolTable (op : FromLCNFArithmetic.Operation) : List UInt8 :=
  ELF.symbol 0 0 0 0 0 ++
  ELF.symbol 0 3 1 0 0 ++
  ELF.symbol 1 0x12 1 0 (textBytes op).length

def textOffset : Nat := 64
def symbolsOffset (op : FromLCNFArithmetic.Operation) : Nat :=
  ELF.alignUp (textOffset + (textBytes op).length) 8
def stringsOffset (op : FromLCNFArithmetic.Operation) : Nat :=
  symbolsOffset op + (symbolTable op).length
def namesOffset (op : FromLCNFArithmetic.Operation) : Nat :=
  stringsOffset op + symbolNames.length
def headersOffset (op : FromLCNFArithmetic.Operation) : Nat :=
  ELF.alignUp (namesOffset op + sectionNames.length) 8

def fileHeader (op : FromLCNFArithmetic.Operation) : List UInt8 :=
  [127, 69, 76, 70, 2, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0] ++
  ELF.le 1 2 ++ ELF.le 62 2 ++ ELF.le 1 4 ++
  ELF.le 0 8 ++ ELF.le 0 8 ++ ELF.le (headersOffset op) 8 ++
  ELF.le 0 4 ++ ELF.le 64 2 ++ ELF.le 0 2 ++ ELF.le 0 2 ++
  ELF.le 64 2 ++ ELF.le 5 2 ++ ELF.le 4 2

def sectionHeaders (op : FromLCNFArithmetic.Operation) : List UInt8 :=
  List.replicate 64 0 ++
  ELF.sectionHeader 1 1 6 textOffset (textBytes op).length 0 0 1 0 ++
  ELF.sectionHeader 7 2 0 (symbolsOffset op) (symbolTable op).length 3 2 8 24 ++
  ELF.sectionHeader 15 3 0 (stringsOffset op) symbolNames.length 0 0 1 0 ++
  ELF.sectionHeader 23 3 0 (namesOffset op) sectionNames.length 0 0 1 0

def objectBytes (op : FromLCNFArithmetic.Operation) : List UInt8 :=
  fileHeader op ++ textBytes op ++
  ELF.padTo (textOffset + (textBytes op).length) (symbolsOffset op) ++
  symbolTable op ++ symbolNames ++ sectionNames ++
  ELF.padTo (namesOffset op + sectionNames.length) (headersOffset op) ++
  sectionHeaders op

/-- The emitted output is derived from the compiler-generated and
    separately source-proof-checked actual LCNF selection. -/
def compile (op : FromLCNFArithmetic.Operation) : ByteArray :=
  (objectBytes op).toByteArray

def layoutValid (op : FromLCNFArithmetic.Operation) : Bool :=
  (fileHeader op).length == 64 &&
  (sectionHeaders op).length == 5 * 64 &&
  (symbolTable op).length == 3 * 24 &&
  (symbolsOffset op) % 8 == 0 &&
  (headersOffset op) % 8 == 0 &&
  (objectBytes op).length == headersOffset op + 5 * 64 &&
  (textBytes op).length == 5

set_option maxRecDepth 16384 in
theorem layout_valid (op : FromLCNFArithmetic.Operation) :
    layoutValid op = true := by
  cases op <;> decide

set_option maxRecDepth 16384 in
theorem emitted_code_decodes (op : FromLCNFArithmetic.Operation) :
    FromLCNFArithmetic.decode
      (((objectBytes op).drop textOffset).take (textBytes op).length) =
    some op := by
  cases op <;> decide

/-- A certificate is tied to the *entire* output file, not its path,
    a user-provided hash, or an unchecked explanatory label. -/
def checkObject (op : FromLCNFArithmetic.Operation) (bytes : ByteArray) : Bool :=
  decide (bytes = compile op)

theorem checkObject_sound (op : FromLCNFArithmetic.Operation) (bytes : ByteArray)
    (h : checkObject op bytes = true) :
    bytes = compile op := by
  exact of_decide_eq_true (by simpa [checkObject] using h)

#print axioms checkObject_sound

end Lean4LeanCompiler.Native.ELFArithmetic
