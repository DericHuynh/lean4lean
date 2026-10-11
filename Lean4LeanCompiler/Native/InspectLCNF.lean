/- Diagnostic: inspect the pinned Lean compiler's actual post-elaboration
   impure LCNF, without claiming a proof or altering the compiler. -/
import Lean.Compiler.Main
import Lean.Compiler.LCNF.PrettyPrinter
import Lean.Elab.Command

namespace Lean4LeanCompiler.Native.InspectLCNF
open Lean Elab Command
open Lean.Compiler.LCNF

syntax (name := l4lcInspectExpr) "#l4lc_inspect_expr " ident : command

@[command_elab l4lcInspectExpr]
meta def inspectExpr : CommandElab
  | `(#l4lc_inspect_expr $decl:ident) => do
    let name ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo decl
    let mut compiled? ← liftCoreM <| getLocalImpureDecl? name
    if compiled?.isNone then
      liftCoreM <| Lean.Compiler.compile #[name]
      compiled? ← liftCoreM <| getLocalImpureDecl? name
    let some compiled := compiled?
      | throwError "[l4lc] no actual impure LCNF for {name}"
    let format ← liftCoreM <| ppDecl' compiled .impure
    logInfo m!"[l4lc-inspect] {name} impure LCNF: {format}"
  | _ => throwUnsupportedSyntax

end Lean4LeanCompiler.Native.InspectLCNF
