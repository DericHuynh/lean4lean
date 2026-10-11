/-
Ordinary source-level Lean declaration. The opt-in compiler pass recognizes
and lowers its actual impure LCNF body (not a separately reconstructed AST).
-/
import Lean4LeanCompiler.Native.FromLCNFCommand

namespace Lean4LeanCompiler.NativeExamples

@[noinline] def returnScalar (x : UInt64) : UInt64 := x

#l4lc_extract_scalar returnScalar as extractedScalar
#check Lean4LeanCompiler.NativeExamples.extractedScalar

/-- Two-parameter scalar ABI; export prevents arity-reduction at boundaries. -/
@[export l4lc_stock_second] def returnSecond (_first second : UInt64) : UInt64 := second

#l4lc_extract_scalar returnSecond as extractedSecond
#check Lean4LeanCompiler.NativeExamples.extractedSecond

end Lean4LeanCompiler.NativeExamples
