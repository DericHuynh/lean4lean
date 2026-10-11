/-
The source-value theorem checks the untrusted actual-LCNF extractor's
generated constant, so an incorrect native operation cannot be accepted
for this particular ordinary Lean declaration.
-/
import Lean4LeanCompiler.NativeArithmeticExamples
import Lean4LeanCompiler.Native.ISA

namespace Lean4LeanCompiler.Native.ArithmeticSourceProof

theorem source_matches_extracted (a b : UInt64) :
    Lean4LeanCompiler.NativeArithmeticExamples.addTwo a b =
      Lean4LeanCompiler.Native.FromLCNFArithmetic.eval
        Lean4LeanCompiler.NativeArithmeticExamples.extractedAddition a b := by
  rfl

/-- This uses the precisely modelled LEA/RET x86 instruction vocabulary.
    It does NOT establish a theorem about real hardware execution. -/
theorem modeled_machine_matches_source (a b : UInt64) :
    (Lean4LeanCompiler.Native.ISA.runAdd
      Lean4LeanCompiler.Native.ISA.addInstructions
      {rdi := a, rsi := b}).rax =
    Lean4LeanCompiler.NativeArithmeticExamples.addTwo a b := by
  rfl

#print axioms source_matches_extracted
#print axioms modeled_machine_matches_source

end Lean4LeanCompiler.Native.ArithmeticSourceProof
