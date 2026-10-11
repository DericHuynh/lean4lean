/-
Direct x86-64 Linux ELF64 ET_REL object generation. No assembler,
C/Rust or LLVM IR is an intermediate language. A C harness is used
ONLY for ABI testing and comparing with an independent implementation.

This module emits relocatable machine code for exactly two certified
kernel signatures: UInt64 addition and four-byte memory copy.

Machine architecture, pointer validity, System V ABI, linker and loader
semantics remain explicitly external assumptions.
-/
import Lean4LeanCompiler.Native.Certified

namespace Lean4LeanCompiler.Native.ELF
open Lean4LeanCompiler.Native

/-- Least-significant byte first, with exactly width output bytes. -/
def le (n width : Nat) : List UInt8 :=
  (List.range width).map fun i => ((n / 256 ^ i) % 256).toUInt8

/-- ELF section alignment is done in bytes. The only used alignment is 8. -/
def alignUp (n alignment : Nat) : Nat :=
  ((n + alignment - 1) / alignment) * alignment

def padTo (used target : Nat) : List UInt8 :=
  List.replicate (target - used) 0

def zstr (s : String) : List UInt8 :=
  s.toUTF8.data.toList ++ [0]

/-- .text, .symtab, .strtab, and .shstrtab section names. -/
def sectionNames : List UInt8 :=
  [0] ++ zstr ".text" ++ zstr ".symtab" ++
  zstr ".strtab" ++ zstr ".shstrtab"

/-- String-table symbol offsets are 1 for l4lc_add64, 12 for l4lc_copy4. -/
def symbolNames : List UInt8 :=
  [0] ++ zstr "l4lc_add64" ++ zstr "l4lc_copy4"

def textBytes : List UInt8 := ISA.addCode ++ ISA.copyCode

/-- ELF64_Sym fields, in the specified little-endian file order. -/
def symbol (name info shndx value size : Nat) : List UInt8 :=
  le name 4 ++ [info.toUInt8, 0] ++ le shndx 2 ++
  le value 8 ++ le size 8

/-- NULL; local .text section; global add and copy symbols. -/
def symbolTable : List UInt8 :=
  symbol 0 0 0 0 0 ++
  symbol 0 3 1 0 0 ++
  symbol 1 0x12 1 0 ISA.addCode.length ++
  symbol 12 0x12 1 ISA.addCode.length ISA.copyCode.length

/-- ELF64 section header layout (64 bytes). -/
def sectionHeader (name typ flags offset size link info alignment entsize : Nat) :
    List UInt8 :=
  le name 4 ++ le typ 4 ++ le flags 8 ++ le 0 8 ++
  le offset 8 ++ le size 8 ++ le link 4 ++ le info 4 ++
  le alignment 8 ++ le entsize 8

def textOffset : Nat := 64
def symbolsOffset : Nat := alignUp (textOffset + textBytes.length) 8
def stringsOffset : Nat := symbolsOffset + symbolTable.length
def namesOffset : Nat := stringsOffset + symbolNames.length
def headersOffset : Nat := alignUp (namesOffset + sectionNames.length) 8

/-- ELF64 header: ET_REL=1, EM_X86_64=62, 5 sections, e_shstrndx=4. -/
def fileHeader : List UInt8 :=
  [127, 69, 76, 70, 2, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0] ++
  le 1 2 ++ le 62 2 ++ le 1 4 ++
  le 0 8 ++ le 0 8 ++ le headersOffset 8 ++
  le 0 4 ++ le 64 2 ++ le 0 2 ++ le 0 2 ++
  le 64 2 ++ le 5 2 ++ le 4 2

/-- SHT_NULL followed by .text, .symtab, .strtab, .shstrtab.
    .symtab.sh_link = 3 (.strtab), sh_info = 2 (first global symbol).
    No relocation entries are necessary: leaf functions make no external calls. -/
def sectionHeaders : List UInt8 :=
  List.replicate 64 0 ++
  sectionHeader 1 1 6 textOffset textBytes.length 0 0 1 0 ++
  sectionHeader 7 2 0 symbolsOffset symbolTable.length 3 2 8 24 ++
  sectionHeader 15 3 0 stringsOffset symbolNames.length 0 0 1 0 ++
  sectionHeader 23 3 0 namesOffset sectionNames.length 0 0 1 0

/-- Complete object bytes, directly from Lean data. -/
def objectBytes : List UInt8 :=
  fileHeader ++ textBytes ++
  padTo (textOffset + textBytes.length) symbolsOffset ++
  symbolTable ++ symbolNames ++ sectionNames ++
  padTo (namesOffset + sectionNames.length) headersOffset ++
  sectionHeaders

/-- This is intentionally restricted to the two source functions for which
    CertifiedProgram has Lean-proved source-value correspondence. -/
def compile (_cert : CertifiedProgram) : ByteArray :=
  objectBytes.toByteArray

/-- Structural checks for the precise no-relocation ELF profile. -/
def layoutValid : Bool :=
  fileHeader.length == 64 &&
  sectionHeaders.length == 5 * 64 &&
  symbolTable.length == 4 * 24 &&
  symbolsOffset % 8 == 0 &&
  headersOffset % 8 == 0 &&
  objectBytes.length == headersOffset + 5 * 64 &&
  textBytes.length == 10

set_option maxRecDepth 16384 in
theorem layoutValid_true : layoutValid = true := by decide

set_option maxRecDepth 16384 in
theorem magic_correct :
    objectBytes.take 4 = [127, 69, 76, 70] := by decide

set_option maxRecDepth 16384 in
theorem code_span_correct :
    (objectBytes.drop textOffset).take textBytes.length = textBytes := by decide

/- Together with ISA.decode* and Certified.sourceCorrect, code_span_correct
    ties the checked instruction subset to the exact emitted .text bytes.
    This does NOT prove the behavior of a real CPU or ELF loader. -/
set_option maxRecDepth 16384 in
theorem emitted_add_opcode :
    ISA.decodeAdd ((objectBytes.drop textOffset).take ISA.addCode.length) =
      some ISA.addInstructions := by decide

set_option maxRecDepth 16384 in
theorem emitted_copy_opcode :
    ISA.decodeCopy
      ((objectBytes.drop (textOffset + ISA.addCode.length)).take ISA.copyCode.length) =
      some ISA.copyInstructions := by decide

end Lean4LeanCompiler.Native.ELF
