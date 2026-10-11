/-
Compiles successfully, because the selected scalar identity has no unknown
LCNF resource sites. Do not mistake syntactic acceptance for runtime safety.
-/
import Lean4LeanCompiler.LCNFEnforce

namespace Lean4LeanCompiler.StrictEnforced

@[noinline] def identity (x : UInt64) : UInt64 := x

end Lean4LeanCompiler.StrictEnforced
