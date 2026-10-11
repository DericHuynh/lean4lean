/-
A theorem-driven, compiler-selected implementation (Lean's @[csimp]),
using one reserved destination for three serializable segments.

This is a logical equality proof, not a physical allocation theorem.
The stock implementation was compiled in Reference.lean before this
csimp theorem is installed; benchmarks compare both compiled versions.
-/
import Lean4LeanCompiler.Reference
import Init.Data.ByteArray.Lemmas
import Lean.Compiler.CSimpAttr

namespace Lean4LeanCompiler.VerifiedJoin

def join3Reserved (a b c : ByteArray) : ByteArray :=
  let dest := ByteArray.emptyWithCapacity (a.size + b.size + c.size)
  ((dest ++ a) ++ b) ++ c

theorem join3Reserved_eq (a b c : ByteArray) :
    Lean4LeanCompiler.Reference.join3 a b c = join3Reserved a b c := by
  change (a ++ b) ++ c =
    ((ByteArray.empty ++ a) ++ b) ++ c
  rw [ByteArray.empty_append]

/-- Adaptive selection: stock for total output smaller than 16 KiB,
    pre-reserved final output storage for larger serialized messages.
    The threshold is a *performance heuristic*, not a semantic precondition. -/
def join3Adaptive (a b c : ByteArray) : ByteArray :=
  if a.size + b.size + c.size < 16384 then
    Lean4LeanCompiler.Reference.join3 a b c
  else
    join3Reserved a b c

theorem join3Adaptive_eq (a b c : ByteArray) :
    Lean4LeanCompiler.Reference.join3 a b c = join3Adaptive a b c := by
  unfold join3Adaptive
  split
  · rfl
  · exact join3Reserved_eq a b c

/-- Actual proof-checked constant replacement applied to new compiled
    declarations, with the dynamic threshold avoiding the measured small-input
    regressions. -/
@[csimp] theorem join3_eq_join3Adaptive :
    @Lean4LeanCompiler.Reference.join3 = @join3Adaptive := by
  funext a b c
  exact join3Adaptive_eq a b c

/-- Compiled as a new call-site after registering the csimp rule. -/
@[noinline] def join3Optimized (a b c : ByteArray) : ByteArray :=
  Lean4LeanCompiler.Reference.join3 a b c

theorem join3Optimized_semantics (a b c : ByteArray) :
    join3Optimized a b c = Lean4LeanCompiler.Reference.join3 a b c := by
  rfl

#print axioms Lean4LeanCompiler.VerifiedJoin.join3_eq_join3Adaptive
#print axioms Lean4LeanCompiler.VerifiedJoin.join3Optimized_semantics

end Lean4LeanCompiler.VerifiedJoin
