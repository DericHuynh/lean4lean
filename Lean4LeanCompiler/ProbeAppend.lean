import Lean.Compiler.LCNF.Passes

namespace Lean4LeanCompiler.ProbeAppend
open Lean
open Lean.Compiler.LCNF

partial def collect : Code .impure → List String
  | .let decl k =>
    let head := match decl.value with
      | .fap name .. => [name.toString]
      | .pap name .. => ["partial:" ++ name.toString]
      | .const name .. => ["const:" ++ name.toString]
      | _ => []
    head ++ collect k
  | .jp (.mk _ _ _ _ body) k => collect body ++ collect k
  | .cases (.mk _ _ _ alts) =>
    alts.toList.flatMap (fun alt => collect alt.getCode)
  | .oset _ _ _ k _ | .uset _ _ _ k _ | .sset _ _ _ _ _ k _
  | .setTag _ _ k _ | .inc _ _ _ _ k _ | .dec _ _ _ _ _ k _
  | .del _ k _ => collect k
  | .return .. | .jmp .. | .unreach .. => []

def probePass : Pass where
  phase := .impure
  phaseOut := .impure
  name := Name.mkSimple "appendProbe"
  run := fun decls => do
    for decl in decls do
      if decl.name.toString.startsWith "Lean4LeanCompiler.ProbeExamples." then
        match decl.value with
        | .code body =>
          let names := collect body
          logInfo m!"[append-probe] {decl.name}: {names}"
        | .extern .. => pure ()
    return decls

@[cpass] meta def installProbe : PassInstaller :=
  PassInstaller.installAfter .impure (Name.mkSimple "simpCase") (fun _ => probePass)

end Lean4LeanCompiler.ProbeAppend
