/-
Logical correspondence between ordinary Lean ByteArray source declarations and
the byte-only resource model. No code-generation or runtime RC claim is made:
ByteArray's Lean definitions model observable values, while its extern
implementations and allocator behavior remain separate trust boundaries.
-/
import Lean4LeanCompiler.Examples
import Lean4LeanCompiler.ResourceProofs

namespace Lean4LeanCompiler.SourceProofs
open Lean4LeanCompiler.ResourceModel

/-- Existing Lean declaration and modeled four-byte copy produce the same
    observable bytes under Lean's source definitions. -/
theorem copyFour_source_model (a b c d : UInt8) :
    ((run copyFour (flatSource [a, b, c, d])).bind State.result?) =
      some ((Lean4LeanCompiler.Examples.copyFour
        ([a, b, c, d] : List UInt8).toByteArray).data.toList) := by
  rfl

/-- Four-byte reversal is correct at the Lean source-language value level. -/
theorem reverseFour_source_bytes (a b c d : UInt8) :
    (Lean4LeanCompiler.Examples.reverseFour
      ([a, b, c, d] : List UInt8).toByteArray).data.toList =
      [d, c, b, a] := by
  rfl

/-- A four-byte initialized output can be used as a destination. This is
    logical source correspondence, not a physical in-place guarantee. -/
theorem writeFourInto_source_bytes (a b c d : UInt8) :
    (Lean4LeanCompiler.Examples.writeFourInto
      ([a, b, c, d] : List UInt8).toByteArray
      ([0, 0, 0, 0] : List UInt8).toByteArray).map
      (fun out => out.data.toList) = some [a, b, c, d] := by
  rfl

#print axioms Lean4LeanCompiler.SourceProofs.copyFour_source_model
#print axioms Lean4LeanCompiler.SourceProofs.reverseFour_source_bytes
#print axioms Lean4LeanCompiler.SourceProofs.writeFourInto_source_bytes
end Lean4LeanCompiler.SourceProofs
