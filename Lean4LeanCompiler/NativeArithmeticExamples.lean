/- Ordinary Lean source definitions, inspected only after stock compiler
   elaboration and reference counting transformations. -/
import Lean4LeanCompiler.Native.InspectLCNF

namespace Lean4LeanCompiler.NativeArithmeticExamples

@[export l4lc_scalar_add]
def addTwo (a b : UInt64) : UInt64 := a + b

#l4lc_inspect_expr addTwo

end Lean4LeanCompiler.NativeArithmeticExamples
