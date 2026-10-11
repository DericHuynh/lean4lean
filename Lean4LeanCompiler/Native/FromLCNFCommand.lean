/-
Explicit native extraction command over actual impure LCNF. It synthesizes
a plain Lean declaration, subsequently checked against the source semantics
by a Lean theorem. No persistent extension mutation or fallback.
-/
import Lean4LeanCompiler.Native.FromLCNF
import Lean.Compiler.Main
import Lean.Elab.Command

namespace Lean4LeanCompiler.Native.Command
open Lean Elab Command
open Lean.Compiler.LCNF

syntax (name := l4lcExtractScalar) "#l4lc_extract_scalar " ident : command

@[command_elab l4lcExtractScalar]
meta def elabScalarExtraction : CommandElab
  | `(#l4lc_extract_scalar $decl:ident) => do
    let name ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo decl
    let mut d? ← liftCoreM <| getLocalImpureDecl? name
    if d?.isNone then
      liftCoreM <| Lean.Compiler.compile #[name]
      d? ← liftCoreM <| getLocalImpureDecl? name
    let some d := d? | throwError "no compiled impure LCNF for {name}; no native fallback"
    let some reg := FromLCNF.recognize d
      | throwError "unsupported scalar LCNF declaration {name}; no native fallback"
    let definition ← match reg with
      | .rdi => `(def _root_.Lean4LeanCompiler.NativeExamples.extractedScalar : Lean4LeanCompiler.Native.FromLCNF.Register := .rdi)
      | .rsi => `(def _root_.Lean4LeanCompiler.NativeExamples.extractedScalar : Lean4LeanCompiler.Native.FromLCNF.Register := .rsi)
    elabCommand definition
    logInfo m!"[l4lc-native] checked actual LCNF extraction for {name}: {repr reg}"
  | _ => throwUnsupportedSyntax

end Lean4LeanCompiler.Native.Command
