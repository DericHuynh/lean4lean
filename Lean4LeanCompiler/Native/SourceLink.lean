/-
A source-level value theorem for the first ordinary Lean declaration lowered
from actual compiler LCNF into a native scalar instruction. This does NOT
establish runtime machine semantics or a verified source/LCNF importer.
-/
import Lean4LeanCompiler.NativeExamples
import Lean4LeanCompiler.Native.ELFScalar

namespace Lean4LeanCompiler.Native.SourceLink

/-- Exact source-value relation to the modeled x86 argument register. -/
theorem returnScalar_matches_native_model (x : UInt64) :
    Lean4LeanCompiler.NativeExamples.returnScalar x =
      Lean4LeanCompiler.Native.FromLCNF.eval Lean4LeanCompiler.NativeExamples.extractedScalar x 0 := by
  rfl

/-- The concrete bytes for this supported modeled return instruction
    are recognized independently of ELF file layout. -/
theorem returnScalar_opcode :
    Lean4LeanCompiler.Native.FromLCNF.decode
      (Lean4LeanCompiler.Native.FromLCNF.encode .rdi) = some .rdi := by
  decide

#print axioms returnScalar_matches_native_model
#print axioms returnScalar_opcode

end Lean4LeanCompiler.Native.SourceLink
