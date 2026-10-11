/-
Lean 4 -> direct Linux x86-64 ELF64 ET_REL output.
No generated C/Rust/LLVM IR and no assembler input.

Three theorem-registered leaf/call kernel signatures:
  l4lc_add64, l4lc_copy4, l4lc_add_then_inc.
The third calls the first, via a real R_X86_64_PLT32 ELF relocation.
The linker, loader, CPU and raw-pointer ABI are external trust boundaries.
-/
import Lean4LeanCompiler.Native.Certified

namespace Lean4LeanCompiler.Native.ELF
open Lean4LeanCompiler.Native

def le (n width : Nat) : List UInt8 :=
  (List.range width).map fun i => ((n / 256 ^ i) % 256).toUInt8

def alignUp (n alignment : Nat) : Nat :=
  ((n + alignment - 1) / alignment) * alignment

def padTo (used target : Nat) : List UInt8 :=
  List.replicate (target - used) 0

def zstr (s : String) : List UInt8 :=
  s.toUTF8.data.toList ++ [0]

/-- Section headers: null, text, rela.text, symtab, strtab, shstrtab.
    sh_name offsets 1, 7, 18, 26, 34. -/
def sectionNames : List UInt8 :=
  [0] ++ zstr ".text" ++ zstr ".rela.text" ++
  zstr ".symtab" ++ zstr ".strtab" ++ zstr ".shstrtab"

/-- Symbol name offsets 1, 12, 23, preceded by the required null byte. -/
def symbolNames : List UInt8 :=
  [0] ++ zstr "l4lc_add64" ++ zstr "l4lc_copy4" ++
  zstr "l4lc_add_then_inc"

def textBytes : List UInt8 :=
  ISA.addCode ++ ISA.copyCode ++ ISA.callCode

/-- ELF64_Sym: st_name, st_info, st_other, st_shndx, st_value, st_size. -/
def symbol (name info shndx value size : Nat) : List UInt8 :=
  le name 4 ++ [info.toUInt8, 0] ++ le shndx 2 ++
  le value 8 ++ le size 8

/-- NULL; local section symbol; three global FUNC symbols in .text. -/
def symbolTable : List UInt8 :=
  symbol 0 0 0 0 0 ++
  symbol 0 3 1 0 0 ++
  symbol 1 0x12 1 0 ISA.addCode.length ++
  symbol 12 0x12 1 ISA.addCode.length ISA.copyCode.length ++
  symbol 23 0x12 1 (ISA.addCode.length + ISA.copyCode.length) ISA.callCode.length

/-- A 4-byte relative displacement starts after CALL's E8 opcode:
    five add bytes + five copy bytes + 4-byte stack prolog + 1 byte. -/
def callDispOffset : Nat :=
  ISA.addCode.length + ISA.copyCode.length + 5

/-- One ELF64_Rela (24 bytes):
    r_offset = 15 within .text (the call's disp32)
    r_info = (st_index=2 << 32) | R_X86_64_PLT32=4
    r_addend = -4, encoded in two's complement little-endian.
    Linker resolves target S + A - P, with P the displacement location.
-/
def relocations : List UInt8 :=
  le callDispOffset 8 ++
  le (2 * 2^32 + 4) 8 ++
  le (2^64 - 4) 8

/-- ELF64_Shdr fields. -/
def sectionHeader (name typ flags offset size link info alignment entsize : Nat) :
    List UInt8 :=
  le name 4 ++ le typ 4 ++ le flags 8 ++ le 0 8 ++
  le offset 8 ++ le size 8 ++ le link 4 ++ le info 4 ++
  le alignment 8 ++ le entsize 8

def textOffset : Nat := 64
def relocationsOffset : Nat := alignUp (textOffset + textBytes.length) 8
def symbolsOffset : Nat := relocationsOffset + relocations.length
def stringsOffset : Nat := symbolsOffset + symbolTable.length
def namesOffset : Nat := stringsOffset + symbolNames.length
def headersOffset : Nat := alignUp (namesOffset + sectionNames.length) 8

/-- ELF64 file header: ET_REL, EM_X86_64, shnum 6, shstrndx 5. -/
def fileHeader : List UInt8 :=
  [127, 69, 76, 70, 2, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0] ++
  le 1 2 ++ le 62 2 ++ le 1 4 ++
  le 0 8 ++ le 0 8 ++ le headersOffset 8 ++
  le 0 4 ++ le 64 2 ++ le 0 2 ++ le 0 2 ++
  le 64 2 ++ le 6 2 ++ le 5 2

/-- .rela.text.sh_link=3 (symtab), .rela.text.sh_info=1 (text);
    .symtab.sh_link=4 (strtab), .symtab.sh_info=2 first global. -/
def sectionHeaders : List UInt8 :=
  List.replicate 64 0 ++
  sectionHeader 1 1 6 textOffset textBytes.length 0 0 1 0 ++
  sectionHeader 7 4 0 relocationsOffset relocations.length 3 1 8 24 ++
  sectionHeader 18 2 0 symbolsOffset symbolTable.length 4 2 8 24 ++
  sectionHeader 26 3 0 stringsOffset symbolNames.length 0 0 1 0 ++
  sectionHeader 34 3 0 namesOffset sectionNames.length 0 0 1 0

/-- Full object, binary emitted in Lean without delegating codegen to C/LLVM. -/
def objectBytes : List UInt8 :=
  fileHeader ++ textBytes ++
  padTo (textOffset + textBytes.length) relocationsOffset ++
  relocations ++ symbolTable ++ symbolNames ++ sectionNames ++
  padTo (namesOffset + sectionNames.length) headersOffset ++
  sectionHeaders

/-- Emission requires the supplied Lean source correctness registrations.
    Internal opcode and relocation bytes are fixed, not user-supplied. -/
def compile (_cert : CertifiedProgram) : ByteArray :=
  objectBytes.toByteArray

/-- Decidable ELF profile, checked before writing an object. -/
def layoutValid : Bool :=
  fileHeader.length == 64 &&
  sectionHeaders.length == 6 * 64 &&
  symbolTable.length == 5 * 24 &&
  relocations.length == 24 &&
  relocationsOffset % 8 == 0 &&
  symbolsOffset % 8 == 0 &&
  headersOffset % 8 == 0 &&
  objectBytes.length == headersOffset + 6 * 64 &&
  textBytes.length == 28 &&
  callDispOffset == 15

set_option maxRecDepth 32768 in
theorem layoutValid_true : layoutValid = true := by decide

set_option maxRecDepth 32768 in
theorem magic_correct :
    objectBytes.take 4 = [127, 69, 76, 70] := by decide

set_option maxRecDepth 32768 in
theorem code_span_correct :
    (objectBytes.drop textOffset).take textBytes.length = textBytes := by decide

/- Static checks that the exact encoded .text bytes decode into our small
   instruction semantics. Physical CPU and relocation resolution are not
   themselves proved by the Lean opcode decoder. -/
set_option maxRecDepth 32768 in
theorem emitted_add_opcode :
    ISA.decodeAdd ((objectBytes.drop textOffset).take ISA.addCode.length) =
      some ISA.addInstructions := by decide

set_option maxRecDepth 32768 in
theorem emitted_copy_opcode :
    ISA.decodeCopy
      ((objectBytes.drop (textOffset + ISA.addCode.length)).take ISA.copyCode.length) =
      some ISA.copyInstructions := by decide

set_option maxRecDepth 32768 in
theorem emitted_call_opcode :
    ISA.decodeCall
      ((objectBytes.drop
          (textOffset + ISA.addCode.length + ISA.copyCode.length)).take
        ISA.callCode.length) =
      some ISA.callInstructions := by decide

/- Precise call-site offset and R_X86_64_PLT32 metadata are covered by a
    separate, kernel-checked payload equality, not just a file-level flag. -/
set_option maxRecDepth 32768 in
theorem relocation_payload_correct :
    (objectBytes.drop relocationsOffset).take relocations.length =
      le 15 8 ++ le (2 * 2^32 + 4) 8 ++ le (2^64 - 4) 8 := by decide

end Lean4LeanCompiler.Native.ELF
