/-
MUST fail to compile. The bound byte-array read goes through an
unknown call/branch and cannot obtain a strict resource certificate.
-/
import Lean4LeanCompiler.LCNFEnforce

namespace Lean4LeanCompiler.StrictEnforced

@[noinline] def uncheckedRead (x : ByteArray) : UInt8 :=
  if x.size == 0 then 0 else x.get! 0

end Lean4LeanCompiler.StrictEnforced
