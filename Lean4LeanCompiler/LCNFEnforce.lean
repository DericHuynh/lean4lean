/-
An opt-in fail-closed compiler mode. Unlike LCNFStrict.gatePass (which
reports diagnostics), this pass throws a compilation error on any
unsupported impure-LCNF declaration. It never calls stock compilation
after rejection.  The accepted property remains ONLY syntactic.
-/
import Lean4LeanCompiler.LCNFStrict

namespace Lean4LeanCompiler.LCNFEnforce
open Lean
open Lean.Compiler.LCNF

def targetPrefix : String := "Lean4LeanCompiler.StrictEnforced."

def enforcePass : Pass where
  phase := .impure
  phaseOut := .impure
  name := Name.mkSimple "l4lcEnforceResourceMode"
  shouldAlwaysRunCheck := true
  run := fun decls => do
    for decl in decls do
      if decl.name.toString.startsWith targetPrefix then
        match Lean4LeanCompiler.LCNFStrict.validate decl with
        | .ok () =>
          logInfo m!"[l4lc-strict] accepted {decl.name}; syntactic-only; machineCertificate=false"
        | .error reason =>
          throwError m!"[l4lc-strict] rejected {decl.name}; {reason}; stock fallback prohibited"
    return decls

@[cpass] meta def installEnforcement : PassInstaller :=
  PassInstaller.installAfter .impure (Name.mkSimple "coalesceRc")
    (fun _ => enforcePass)

end Lean4LeanCompiler.LCNFEnforce
