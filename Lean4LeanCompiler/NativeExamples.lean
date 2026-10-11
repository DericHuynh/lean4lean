/-
Ordinary source-level Lean declaration. The opt-in compiler pass recognizes
and lowers its actual impure LCNF body (not a separately reconstructed AST).
-/
import Lean4LeanCompiler.Native.FromLCNFCommand

namespace Lean4LeanCompiler.NativeExamples

@[noinline] def returnScalar (x : UInt64) : UInt64 := x

#l4lc_extract_scalar returnScalar
#check Lean4LeanCompiler.NativeExamples.extractedScalar

end Lean4LeanCompiler.NativeExamples
