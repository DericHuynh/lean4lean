import Lean4LeanCompiler.MorphicModeProbe
import Lean.Compiler.LCNF.Passes

namespace Lean4LeanCompiler.MorphicModeInstaller

open Lean
open Lean.Compiler.LCNF

@[cpass] meta def installModes : PassInstaller :=
  PassInstaller.installBefore .impure (Name.mkSimple "inferBorrow")
    (fun _ => MorphicBorrow.inferMorphicBorrow)

@[cpass] meta def auditModes : PassInstaller :=
  PassInstaller.installAfter .impure (Name.mkSimple "inferBorrow")
    (fun _ => MorphicBorrow.auditMorphicBorrow)

end Lean4LeanCompiler.MorphicModeInstaller
