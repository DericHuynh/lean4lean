/- Ordinary Lean source definitions, inspected only after stock compiler
   elaboration and reference counting transformations. -/
import Lean4LeanCompiler.Native.InspectLCNF
import Lean4LeanCompiler.Native.ExtractArithmeticCommand

namespace Lean4LeanCompiler.NativeArithmeticExamples

@[export l4lc_scalar_add]
def addTwo (a b : UInt64) : UInt64 := a + b

#l4lc_inspect_expr addTwo
#l4lc_extract_add addTwo as extractedAddition
#check Lean4LeanCompiler.NativeArithmeticExamples.extractedAddition

end Lean4LeanCompiler.NativeArithmeticExamples
