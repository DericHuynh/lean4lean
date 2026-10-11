import Lean.Compiler.LCNF.Passes
import Lean4LeanCompiler.MorphicLifetimePilot

namespace Lean4LeanCompiler.MorphicLifetimeInstaller
open Lean
open Lean.Compiler.LCNF

set_option compiler.relaxedMetaCheck true in
@[cpass] meta def installMorphicBorrow : PassInstaller :=
  PassInstaller.installBefore .impure (Name.mkSimple "inferBorrow")
    (fun _ => MorphicBorrow.inferMorphicBorrow)

set_option compiler.relaxedMetaCheck true in
@[cpass] meta def auditMorphicBorrow : PassInstaller :=
  PassInstaller.installAfter .impure (Name.mkSimple "inferBorrow")
    (fun _ => MorphicBorrow.auditMorphicBorrow)

set_option compiler.relaxedMetaCheck true in
@[cpass] meta def auditRcSites : PassInstaller :=
  PassInstaller.installAfter .impure (Name.mkSimple "explicitRc")
    (fun _ => MorphicBorrow.auditRetains)

end Lean4LeanCompiler.MorphicLifetimeInstaller
