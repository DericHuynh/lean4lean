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
def addCode : List UInt8 := [0x48, 0x89, 0xf8, 0x48, 0x01, 0xf0, 0xc3]

/-- x86-64 SysV: mov eax,[rdi]; mov [rsi],eax; ret.
    Assumes valid addressable 4-byte ranges on the native machine.
    The complete four-byte load happens before the complete store. -/
def copyCode : List UInt8 := [0x8b, 0x07, 0x89, 0x06, 0xc3]

inductive AddInstruction where
  | movRaxRdi | addRaxRsi | ret
  deriving DecidableEq, Inhabited

inductive CopyInstruction where
  | loadEaxFromRdi | storeEaxToRsi | ret
  deriving DecidableEq, Inhabited

def addInstructions : List AddInstruction :=
  [.movRaxRdi, .addRaxRsi, .ret]

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
  | .ret => reg

def runAdd (instrs : List AddInstruction) (reg : AddRegisters) : AddRegisters :=
  instrs.foldl stepAdd reg

/-- The generated machine-code vocabulary's modeled add computes the
    exact semantics of Lean UInt64 addition, including wraparound. -/
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

end Lean4LeanCompiler.Native.ISA
