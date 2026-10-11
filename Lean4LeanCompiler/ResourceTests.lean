/-
Lean kernel-checked executable positive and adversarial model tests.
Theorems about the small semantics, NOT runtime allocation measurements.
-/
import Lean4LeanCompiler.ResourceProofs

namespace Lean4LeanCompiler.ResourceTests
open Lean4LeanCompiler.ResourceModel

private def input : State := flatSource [11, 22, 33, 44]

example : check noAllocation copyFour input = true := by decide
example : ((run copyFour input).bind State.result?) =
    some [11, 22, 33, 44] := by decide
example : check noAllocation copyFour (flatSource []) = false := by decide
example : check noAllocation copyFour (flatSource [1, 2, 3]) = false := by decide

/-- Allocating the output inside the writer violates the writer contract. -/
example : check noAllocation
    [.beginRegion, .fresh 1, .append 11, .publish, .endRegion] input = false := by decide
example : check ⟨1, 1⟩
    [.beginRegion, .fresh 1, .append 11, .publish, .endRegion] input = true := by decide
example : check noAllocation
    [.fresh 0, .beginRegion, .publish, .endRegion] input = true := by decide

/-- Bounds checks and complete destination initialization. -/
example : check noAllocation
    [.fresh 1, .beginRegion, .append 1, .append 2, .publish, .endRegion]
    input = false := by decide
example : check noAllocation
    [.fresh 2, .beginRegion, .append 1, .publish, .endRegion]
    input = false := by decide
example : check noAllocation
    [.beginRegion, .append 1, .endRegion] input = false := by decide

/-- Linear owner cannot be consumed while a borrow exists; no escape. -/
example : check noAllocation
    [.fresh 0, .beginRegion, .borrow, .publish, .endRegion]
    input = false := by decide
example : check noAllocation
    [.fresh 0, .beginRegion, .borrow, .dropSource, .release,
     .publish, .endRegion] input = false := by decide
example : check noAllocation
    [.fresh 0, .beginRegion, .release, .publish, .endRegion]
    input = false := by decide

/-- Reuse requires both uniqueness and sufficient storage. -/
example : check noAllocation reverseFourReuse input = false := by decide
example : check noAllocation reverseFourReuse
    (flatSource [11, 22, 33, 44] true) = true := by decide
example : ((run reverseFourReuse (flatSource [11, 22, 33, 44] true)).bind State.result?) =
    some [44, 33, 22, 11] := by decide
example : check noAllocation reverseFourReuse
    (flatSource [11, 22, 33] true) = false := by decide
example : check noAllocation
    [.beginRegion, .borrow, .reuseSource 4, .release,
     .append 1, .append 2, .append 3, .append 4, .publish, .endRegion]
    (flatSource [11, 22, 33, 44] true) = false := by decide

/-- Loads require a live borrow, valid index and distinct register. -/
example : check noAllocation
    [.beginRegion, .load 0 0, .reuseSource 1,
     .appendRegister 0, .publish, .endRegion]
    (flatSource [7] true) = false := by decide
example : check noAllocation
    [.beginRegion, .borrow, .load 99 0, .release,
     .reuseSource 1, .appendRegister 0, .publish, .endRegion]
    (flatSource [7] true) = false := by decide
example : check noAllocation
    [.beginRegion, .borrow, .load 0 0, .load 0 0, .release,
     .reuseSource 1, .appendRegister 0, .publish, .endRegion]
    (flatSource [7] true) = false := by decide

/-- Failure to publish, repeated publication and unsupported effects fail. -/
example : check noAllocation
    [.fresh 0, .beginRegion, .unsupported, .publish, .endRegion]
    input = false := by decide
example : check noAllocation
    [.fresh 0, .beginRegion, .publish, .publish, .endRegion]
    input = false := by decide
example : check noAllocation
    [.fresh 0, .beginRegion, .publish] input = false := by decide

/-- The model-level no-op deletion is both proved and tested. -/
example : eraseNops [.nop, .borrow, .nop, .release] =
    [.borrow, .release] := by decide
example : check noAllocation (eraseNops (.nop :: copyFour)) input = true := by decide

end Lean4LeanCompiler.ResourceTests
