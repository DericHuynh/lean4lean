/-
Explicit compiler command extracts a checked operation from the actual
impure LCNF of a named ordinary Lean declaration. It creates a normal
Lean constant, so a separate source-value theorem can reject bad output.
No exception-suppressed fallback, no unchecked native artifact emission.
-/
import Lean4LeanCompiler.Native.FromLCNFArithmetic
import Lean.Compiler.Main
import Lean.Elab.Command

namespace Lean4LeanCompiler.Native.ExtractArithmeticCommand
open Lean Elab Command Lean.Compiler.LCNF

syntax (name := l4lcExtractAdd) "#l4lc_extract_add " ident " as " ident : command

@[command_elab l4lcExtractAdd]
meta def elabExtractAdd : CommandElab
  | `(#l4lc_extract_add $decl:ident as $outIdent:ident) => do
    let name ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo decl
    let mut compiled? ← liftCoreM <| getLocalImpureDecl? name
    if compiled?.isNone then
      liftCoreM <| Lean.Compiler.compile #[name]
      compiled? ← liftCoreM <| getLocalImpureDecl? name
    let some compiled := compiled?
      | throwError "[l4lc-add] no compiled impure LCNF for {name}; no fallback"
    let some op := FromLCNFArithmetic.recognize compiled
      | throwError "[l4lc-add] unsupported/allocating/effectful LCNF in {name}; no fallback"
    let definition ← `(def $outIdent:ident :
       Lean4LeanCompiler.Native.FromLCNFArithmetic.Operation := .add)
    elabCommand definition
    logInfo m!"[l4lc-add] recognized {name} from real impure LCNF: {repr op}; certifiedNative=false"
  | _ => throwUnsupportedSyntax

end Lean4LeanCompiler.Native.ExtractArithmeticCommand
