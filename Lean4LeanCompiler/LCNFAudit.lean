/-
A separate compiler hook sees actual elaborated Lean declarations at impure
LCNF, after stock ownership analysis, before stock code emission. It only
records current borrowing decisions and makes NO verification claim.
-/
import Lean.Compiler.LCNF.Passes

namespace Lean4LeanCompiler.LCNFAudit
open Lean
open Lean.Compiler.LCNF

def auditPass : Pass where
  phase := .impure
  name := Name.mkSimple "l4lcAudit"
  run := fun decls => do
    for decl in decls do
      if decl.name.toString == "Lean4LeanCompiler.Examples.copyFour" ||
         decl.name.toString == "Lean4LeanCompiler.Examples.reverseFour" ||
         decl.name.toString == "Lean4LeanCompiler.Examples.writeFourInto" ||
         decl.name.toString == "Lean4LeanCompiler.Examples.bumpList" then
        let borrowed := decl.params.foldl
          (fun n p => if p.borrow then n + 1 else n) (0 : Nat)
        logInfo m!"[l4lc] {decl.name}: borrowed parameters={borrowed}; certified=false"
    return decls

@[cpass] meta def installAudit : PassInstaller :=
  PassInstaller.installAfter .impure (Name.mkSimple "coalesceRc") (fun _ => auditPass)

end Lean4LeanCompiler.LCNFAudit
