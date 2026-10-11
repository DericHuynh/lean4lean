/-
Installer is a separate module so the persistent environment extension,
its initializer, and the actual pass code are already in compiled imports
before the @[cpass] attribute evaluates this declaration.
-/
import Lean4LeanCompiler.Native.FromLCNF

namespace Lean4LeanCompiler.Native
open Lean
open Lean.Compiler.LCNF

@[cpass] meta def installNativeExtraction : PassInstaller :=
  PassInstaller.installAfter .impure (Name.mkSimple "coalesceRc")
    (fun _ => FromLCNF.nativeExtractionPass)

end Lean4LeanCompiler.Native
