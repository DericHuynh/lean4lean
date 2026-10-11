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

/-- Actual compiler constant substitution, checked by a Lean theorem.
    It applies to calls compiled *after* importing this module. -/
@[csimp] theorem join3_eq_join3Reserved :
    @Lean4LeanCompiler.Reference.join3 = @join3Reserved := by
  funext a b c
  exact join3Reserved_eq a b c

/-- Compiled as a new call-site after registering the csimp rule. -/
@[noinline] def join3Optimized (a b c : ByteArray) : ByteArray :=
  Lean4LeanCompiler.Reference.join3 a b c

theorem join3Optimized_semantics (a b c : ByteArray) :
    join3Optimized a b c = Lean4LeanCompiler.Reference.join3 a b c := by
  rfl

#print axioms Lean4LeanCompiler.VerifiedJoin.join3_eq_join3Reserved
#print axioms Lean4LeanCompiler.VerifiedJoin.join3Optimized_semantics

end Lean4LeanCompiler.VerifiedJoin
