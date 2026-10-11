import Lean

namespace Lean4LeanCompiler.AppendProbeStock

/-- Compiled without importing the new append fusion pass. -/
@[noinline] def tripleAppend (a b c : ByteArray) : ByteArray := (a ++ b) ++ c

end Lean4LeanCompiler.AppendProbeStock
