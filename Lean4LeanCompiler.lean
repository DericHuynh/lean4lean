/-
Separate experimental compiler component; does not modify Lean4Lean kernel,
Lean4Lean.Verify, or the lean4lean executable.
-/
import Lean4LeanCompiler.ResourceModel
import Lean4LeanCompiler.ResourceProofs
import Lean4LeanCompiler.ResourceTests
import Lean4LeanCompiler.Examples
import Lean4LeanCompiler.SourceProofs
import Lean4LeanCompiler.Native
import Lean4LeanCompiler.VerifiedJoin
import Lean4LeanCompiler.StrictExamples
import Lean4LeanCompiler.NativeExamples
import Lean4LeanCompiler.Native.ELFScalar
import Lean4LeanCompiler.Native.SourceLink
import Lean4LeanCompiler.Native.ELFArithmetic
