/-
Proofs concern the executable model, not Lean's runtime, representation
erasure, imported declarations, or emitted object code. No sorry or axioms
are introduced by this module.
-/
import Lean4LeanCompiler.ResourceModel

namespace Lean4LeanCompiler.ResourceProofs
open Lean4LeanCompiler.ResourceModel

/-- Semantic preservation for any four input bytes in the modeled fresh,
    destination-passing copy routine. -/
theorem copyFour_bytes (a b c d : UInt8) :
    ((run copyFour (flatSource [a, b, c, d])).bind State.result?) =
      some [a, b, c, d] := by
  rfl

/-- The final fresh allocation occurs before the metered writer. -/
theorem copyFour_no_region_alloc (a b c d : UInt8) :
    check noAllocation copyFour (flatSource [a, b, c, d]) = true := by
  rfl

/-- Modeled fresh output does not consume or overwrite its source. -/
theorem copyFour_preserves_source (a b c d : UInt8) :
    (run copyFour (flatSource [a, b, c, d])).map State.source =
      some (.live [a, b, c, d] 0 false) := by
  rfl

/-- Four saved scalar registers remain usable after consuming the unique
    flat source allocation. This is not a theorem about descendant objects. -/
theorem reverseFour_bytes (a b c d : UInt8) :
    ((run reverseFourReuse (flatSource [a, b, c, d] true)).bind State.result?) =
      some [d, c, b, a] := by
  rfl

/-- Reuse contributes zero new allocations in this explicit byte-only model. -/
theorem reverseFour_no_region_alloc (a b c d : UInt8) :
    check noAllocation reverseFourReuse
      (flatSource [a, b, c, d] true) = true := by
  rfl

/-- A shared input never obtains the unique-only reuse certificate. -/
theorem reverseFour_shared_rejected (a b c d : UInt8) :
    check noAllocation reverseFourReuse
      (flatSource [a, b, c, d] false) = false := by
  rfl

#print axioms Lean4LeanCompiler.ResourceModel.check_sound
#print axioms Lean4LeanCompiler.ResourceModel.run_eraseNops
#print axioms Lean4LeanCompiler.ResourceProofs.copyFour_bytes
#print axioms Lean4LeanCompiler.ResourceProofs.reverseFour_bytes
end Lean4LeanCompiler.ResourceProofs
