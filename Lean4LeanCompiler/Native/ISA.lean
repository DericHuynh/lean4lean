/-
A finite, reviewable x86-64 instruction subset used by Native.ELF.
These are *modeled* instruction semantics. Correspondence to the physical
processor is checked by native executable tests, not mechanically proved.
No external CPU, memory/ABI, or ELF loader is in the trusted model.
-/
import Lean4LeanCompiler.ResourceModel

namespace Lean4LeanCompiler.Native.ISA

/-- x86-64 SysV: mov rax,rdi; add rax,rsi; ret.
    64-bit unsigned arithmetic wraps modulo 2^64. -/
def addCodeBaseline : List UInt8 := [0x48, 0x89, 0xf8, 0x48, 0x01, 0xf0, 0xc3]

/-- One LEA and RET instead of a MOV/ADD/RET pair. LEA computes the
    effective address but never dereferences a pointer. -/
def addCode : List UInt8 := [0x48, 0x8d, 0x04, 0x37, 0xc3]

theorem addCode_smaller : addCode.length < addCodeBaseline.length := by decide

/-- x86-64 SysV: mov eax,[rdi]; mov [rsi],eax; ret.
    Assumes valid addressable 4-byte ranges on the native machine.
    The complete four-byte load happens before the complete store. -/
def copyCode : List UInt8 := [0x8b, 0x07, 0x89, 0x06, 0xc3]

inductive AddInstruction where
  | movRaxRdi | addRaxRsi | leaRaxRdiRsi | ret
  deriving DecidableEq, Inhabited

inductive CopyInstruction where
  | loadEaxFromRdi | storeEaxToRsi | ret
  deriving DecidableEq, Inhabited

def addInstructionsBaseline : List AddInstruction :=
  [.movRaxRdi, .addRaxRsi, .ret]

def addInstructions : List AddInstruction :=
  [.leaRaxRdiRsi, .ret]

def copyInstructions : List CopyInstruction :=
  [.loadEaxFromRdi, .storeEaxToRsi, .ret]

/-- An intentionally *closed* decoder. Unsupported bytes are rejected.
    This proof validates the compiler's own limited opcode vocabulary. -/
def decodeAdd (bytes : List UInt8) : Option (List AddInstruction) :=
  if bytes == addCode then some addInstructions else none

def decodeCopy (bytes : List UInt8) : Option (List CopyInstruction) :=
  if bytes == copyCode then some copyInstructions else none

theorem decodeAdd_emitted : decodeAdd addCode = some addInstructions := by decide
theorem decodeCopy_emitted : decodeCopy copyCode = some copyInstructions := by decide

example : decodeAdd [0xc3] = none := by decide
example : decodeCopy [0xc3] = none := by decide

structure AddRegisters where
  rax : UInt64 := 0
  rdi : UInt64
  rsi : UInt64
  deriving Inhabited

def stepAdd (reg : AddRegisters) : AddInstruction → AddRegisters
  | .movRaxRdi => { reg with rax := reg.rdi }
  | .addRaxRsi => { reg with rax := reg.rax + reg.rsi }
  | .leaRaxRdiRsi => { reg with rax := reg.rdi + reg.rsi }
  | .ret => reg

def runAdd (instrs : List AddInstruction) (reg : AddRegisters) : AddRegisters :=
  instrs.foldl stepAdd reg

/-- The generated machine-code vocabulary's modeled add computes the
    exact semantics of Lean UInt64 addition, including wraparound. -/
theorem addBaseline_correct (a b : UInt64) :
    (runAdd addInstructionsBaseline { rdi := a, rsi := b }).rax = a + b := by rfl

theorem addCode_correct (a b : UInt64) :
    (runAdd addInstructions { rdi := a, rsi := b }).rax = a + b := by rfl

structure CopyRegisters where
  src : List UInt8
  dst : List UInt8
  eax : Option (List UInt8) := none
  deriving DecidableEq

/-- Loading and storing bytes are separate events; the load precedes the
    write. This model includes length checks, which the emitted CPU does NOT.
    Valid native pointer/capacity preconditions are required at the ABI. -/
def stepCopy (reg : CopyRegisters) : CopyInstruction → Option CopyRegisters
  | .loadEaxFromRdi =>
    if 4 ≤ reg.src.length then
      some { reg with eax := some (reg.src.take 4) }
    else none
  | .storeEaxToRsi =>
    if 4 ≤ reg.dst.length then
      match reg.eax with
      | some value => some { reg with dst := value ++ reg.dst.drop 4 }
      | none => none
    else none
  | .ret => some reg

def runCopy : List CopyInstruction → CopyRegisters → Option CopyRegisters
  | [], reg => some reg
  | op :: ops, reg => do
    let next ← stepCopy reg op
    runCopy ops next

/-- Complete observable output bytes for the supported exact-width case. -/
theorem copyCode_exact (a b c d : UInt8) :
    (runCopy copyInstructions
      { src := [a, b, c, d], dst := [0, 0, 0, 0] }).map
      (fun reg => reg.dst) = some [a, b, c, d] := by rfl

/-- Short input cannot satisfy the modeled native calling contract. -/
example :
    runCopy copyInstructions
      { src := [1, 2, 3], dst := [0, 0, 0, 0] } = none := by decide

/-- Short output cannot satisfy the modeled native calling contract. -/
example :
    runCopy copyInstructions
      { src := [1, 2, 3, 4], dst := [0, 0, 0] } = none := by decide


/-- Call expansion: sub rsp,8; call l4lc_add64; add rsp,8;
    add rax,1; ret. CALL's disp32 is a zero placeholder to be patched
    using a real ELF R_X86_64_PLT32 relocation with addend -4.
    On function entry rsp%16=8; before CALL it must be 0. -/
def callCode : List UInt8 :=
  [0x48, 0x83, 0xec, 0x08, 0xe8, 0, 0, 0, 0,
   0x48, 0x83, 0xc4, 0x08, 0x48, 0x83, 0xc0, 0x01, 0xc3]

inductive CallInstruction where
  | alignStack | callAdd | restoreStack | incrementResult | ret
  deriving DecidableEq, Inhabited

def callInstructions : List CallInstruction :=
  [.alignStack, .callAdd, .restoreStack, .incrementResult, .ret]

def decodeCall (bytes : List UInt8) : Option (List CallInstruction) :=
  if bytes == callCode then some callInstructions else none

theorem decodeCall_emitted :
    decodeCall callCode = some callInstructions := by decide

structure CallRegisters where
  rdi : UInt64
  rsi : UInt64
  rax : UInt64 := 0
  rspMod16 : Nat := 8

/-- Stack-alignment and one known direct-call summary. This is an abstract
    model of System V ABI, NOT a theorem about the system assembler/linker. -/
def stepCall (regs : CallRegisters) : CallInstruction → Option CallRegisters
  | .alignStack =>
      if regs.rspMod16 == 8 then
        some { regs with rspMod16 := 0 }
      else none
  | .callAdd =>
      if regs.rspMod16 == 0 then
        some { regs with rax := regs.rdi + regs.rsi }
      else none
  | .restoreStack =>
      if regs.rspMod16 == 0 then
        some { regs with rspMod16 := 8 }
      else none
  | .incrementResult =>
      some { regs with rax := regs.rax + 1 }
  | .ret =>
      if regs.rspMod16 == 8 then some regs else none

def runCall : List CallInstruction → CallRegisters → Option CallRegisters
  | [], regs => some regs
  | i :: is, regs => do
      let next ← stepCall regs i
      runCall is next

/-- The modeled known-target call preserves both argument registers,
    16-byte caller stack alignment and modular arithmetic. -/
theorem callCode_correct (a b : UInt64) :
    (runCall callInstructions { rdi := a, rsi := b }).map
      (fun regs => (regs.rax, regs.rspMod16)) =
      some (a + b + 1, 8) := by rfl

/-- If the caller starts with incorrect stack alignment, reject the
    calling contract instead of treating arbitrary stack contents as valid. -/
example (a b : UInt64) :
    runCall callInstructions { rdi := a, rsi := b, rspMod16 := 0 } = none := by
  rfl

end Lean4LeanCompiler.Native.ISA
