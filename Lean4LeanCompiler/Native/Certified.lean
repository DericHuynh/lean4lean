/-
A checked connection to ordinary Lean declarations. Instead of trusting
names, registration requires an actual Lean proof connecting the source
function to the native subset's modeled semantics.
These proofs do NOT prove the CPU's instruction decoder/ABI implementation.
-/
import Lean4LeanCompiler.Native.ISA
import Lean4LeanCompiler.Reference

namespace Lean4LeanCompiler.Native

/-- An ordinary existing Lean function, not a handwritten compiler AST. -/
def sourceAdd64 (a b : UInt64) : UInt64 := a + b

structure CertifiedAdd where
  source : UInt64 → UInt64 → UInt64
  sourceCorrect : ∀ a b, source a b = a + b

/-- Compilation cannot select the add opcode without a source-level proof. -/
def addRegistration : CertifiedAdd :=
  { source := sourceAdd64
    sourceCorrect := by intro a b; rfl }

/-- ELF export l4lc_copy4 accepts (const uint8_t*, uint8_t*) under an explicit
    four-readable/four-writable-byte native ABI contract. The corresponding
    ordinary Lean function manipulates ByteArrays. The two representations
    are NOT asserted to have interchangeable machine layouts. -/
structure CertifiedCopy4 where
  source : ByteArray → ByteArray → Option ByteArray
  sourceCorrect : ∀ a b c d : UInt8,
    (source
      ([a, b, c, d] : List UInt8).toByteArray
      ([0, 0, 0, 0] : List UInt8).toByteArray).map
      (fun out => out.data.toList) = some [a, b, c, d]

def copyRegistration : CertifiedCopy4 :=
  { source := Lean4LeanCompiler.Reference.writeFourInto
    sourceCorrect := by intro a b c d; rfl }

theorem modeledAdd_matchesSource (cert : CertifiedAdd) (a b : UInt64) :
    (ISA.runAdd ISA.addInstructions { rdi := a, rsi := b }).rax =
      cert.source a b := by
  calc
    _ = a + b := ISA.addCode_correct a b
    _ = cert.source a b := (cert.sourceCorrect a b).symm

theorem modeledCopy_matchesSource (cert : CertifiedCopy4) (a b c d : UInt8) :
    (ISA.runCopy ISA.copyInstructions
       { src := [a, b, c, d], dst := [0, 0, 0, 0] }).map
       (fun reg => reg.dst) =
      (cert.source
        ([a, b, c, d] : List UInt8).toByteArray
        ([0, 0, 0, 0] : List UInt8).toByteArray).map
        (fun out => out.data.toList) := by
  calc
    _ = some [a, b, c, d] := ISA.copyCode_exact a b c d
    _ = _ := (cert.sourceCorrect a b c d).symm


/-- A separate ordinary Lean declaration with a direct call relationship. -/
def sourceAddThenInc (a b : UInt64) : UInt64 := sourceAdd64 a b + 1

structure CertifiedCall where
  source : UInt64 → UInt64 → UInt64
  sourceCorrect : ∀ a b, source a b = a + b + 1

def callRegistration : CertifiedCall :=
  { source := sourceAddThenInc
    sourceCorrect := by intro a b; rfl }

theorem modeledCall_matchesSource (cert : CertifiedCall) (a b : UInt64) :
    (ISA.runCall ISA.callInstructions { rdi := a, rsi := b }).map
      (fun regs => regs.rax) = some (cert.source a b) := by
  calc
    _ = some (a + b + 1) := by rfl
    _ = some (cert.source a b) := by rw [cert.sourceCorrect]

#print axioms Lean4LeanCompiler.Native.modeledCall_matchesSource

/-- Native emission is available only for the certified registrations above. -/
structure CertifiedProgram where
  add : CertifiedAdd
  copy : CertifiedCopy4
  call : CertifiedCall

def registered : CertifiedProgram :=
  { add := addRegistration, copy := copyRegistration, call := callRegistration }

#print axioms Lean4LeanCompiler.Native.modeledAdd_matchesSource
#print axioms Lean4LeanCompiler.Native.modeledCopy_matchesSource
#print axioms Lean4LeanCompiler.Native.ISA.addCode_correct
#print axioms Lean4LeanCompiler.Native.ISA.copyCode_exact

end Lean4LeanCompiler.Native
