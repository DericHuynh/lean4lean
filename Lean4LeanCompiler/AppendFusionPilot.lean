import Lean.Compiler.LCNF.PassManager
import Init.Data.ByteArray.Lemmas

namespace Lean4LeanCompiler.AppendFusionPilot
open Lean
open Lean.Compiler.LCNF

@[inline] def fastAppend3 (a b c : ByteArray) : ByteArray :=
  if a.size + b.size + c.size < 16384 then
    (a.fastAppend b).fastAppend c
  else
    let dst := ByteArray.emptyWithCapacity (a.size + b.size + c.size)
    let dst := dst.fastAppend a
    let dst := dst.fastAppend b
    dst.fastAppend c

theorem fastAppend3_eq_append (a b c : ByteArray) :
    fastAppend3 a b c = (a ++ b) ++ c := by
  have he : ByteArray.emptyWithCapacity (a.size + b.size + c.size) =
      ByteArray.empty := rfl
  by_cases h : a.size + b.size + c.size < 16384
  · simp [fastAppend3, h, ByteArray.fastAppend_eq]
  · simp [fastAppend3, h, ByteArray.fastAppend_eq, he]

theorem fastAppend3_size (a b c : ByteArray) :
    (fastAppend3 a b c).size = a.size + b.size + c.size := by
  rw [fastAppend3_eq_append]
  simp [ByteArray.size_append]

#print axioms fastAppend3_size

#print axioms fastAppend3_eq_append

private def helperName : Name :=
  Name.str (Name.str (Name.mkSimple "Lean4LeanCompiler") "AppendFusionPilot") "fastAppend3"

private def appendName (n : Name) : Bool :=
  n.toString == "ByteArray.fastAppend"

/-- Compiler-recognized, exact two-append call chain with no escaping
    intermediate result. For overloaded ++, require the precise ByteArray
    dictionary and HAppend projection, not an arbitrary FVar. -/
private def matchChain? : Code .pure → Option (LetDecl .pure ×
    Arg .pure × Arg .pure × Arg .pure) 
  | .let f (.let s (.return r)) =>
    if r != s.fvarId then none
    else
      match f.value, s.value with
      | .const n _ args _, .const m _ args' _ =>
        if appendName n && appendName m &&
           args.size == 2 && args'.size == 2 &&
           args'[0]! == .fvar f.fvarId then
          some (s, args[0]!, args[1]!, args'[1]!)
        else none
      | _, _ => none
  | .let inst (.let happ (.let proj (.let f (.let s (.return r))))) =>
    if r != s.fvarId then none
    else
      match inst.value, happ.value, proj.value, f.value, s.value with
      | .const n _ iargs _, .const hn _ hargs _, .proj pn ix src _,
        .fvar fn args, .fvar fn' args' =>
        if n.toString == "ByteArray.instAppend" &&
           iargs.isEmpty &&
           hn.toString == "instHAppendOfAppend" &&
           hargs.size == 2 &&
           hargs[1]! == .fvar inst.fvarId &&
           pn.toString == "HAppend" && ix == 0 &&
           src == happ.fvarId &&
           fn == proj.fvarId && fn' == proj.fvarId &&
           args.size == 2 && args'.size == 2 &&
           args'[0]! == .fvar f.fvarId then
          some (s, args[0]!, args[1]!, args'[1]!)
        else none
      | _, _, _, _, _ => none
  | _ => none

partial def fuseCode (code : Code .pure) : CompilerM (Code .pure) := do
  if let some (final, a, b, c) := matchChain? code then
    logInfo m!"[append-fused] exactly matched safe chain"
    return .let { final with value := .const helperName [] #[a, b, c] }
      (.return final.fvarId)
  match code with
  | .let d k => return .let d (← fuseCode k)
  | .fun (.mk f n ps ty body) k _ =>
    return .fun (.mk f n ps ty (← fuseCode body)) (← fuseCode k)
  | .jp (.mk f n ps ty body) k =>
    return .jp (.mk f n ps ty (← fuseCode body)) (← fuseCode k)
  | .cases (.mk ty result discr alts) =>
    return .cases (.mk ty result discr
      (← alts.mapM (·.mapCodeM fuseCode)))
  | .return .. | .jmp .. | .unreach .. => return code

def pass : Pass :=
  Pass.mkPerDeclaration (Name.mkSimple "appendPilot") .base
    (fun decl => do
      let value ← decl.value.mapCodeM fuseCode
      return { decl with value })

@[cpass] meta def installPilot : PassInstaller :=
  PassInstaller.installAfter .base (Name.mkSimple "pullInstances") (fun _ => pass)

end Lean4LeanCompiler.AppendFusionPilot
