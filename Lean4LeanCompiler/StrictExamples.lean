/-
Real ordinary Lean declarations scanned by the resource gate at impure LCNF.
Even success means only zero *static unchecked sites* and a safe declaration:
the compiler's erasure and machine runtime are not formally verified.
-/
import Lean4LeanCompiler.LCNFStrict

namespace Lean4LeanCompiler.StrictExamples

@[noinline] def returnArgument (x : UInt64) : UInt64 := x

@[noinline] def readByte (x : ByteArray) : UInt8 :=
  if x.size == 0 then 0 else x.get! 0

@[noinline] def allocateList (xs : List UInt8) : List UInt8 :=
  xs.map (· + 1)

end Lean4LeanCompiler.StrictExamples
