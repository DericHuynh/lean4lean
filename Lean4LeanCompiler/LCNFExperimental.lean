/-
Experimental actual Lean declaration transformer, for Lean v4.33.0-rc2.
It removes zero-count RC operations after stock explicit RC insertion,
before stock RC coalescing. It deliberately does NOT claim to implement
Morphic borrow inference, destination passing, or FP2. The model proofs
elsewhere do not certify this rewrite or emitted machine instructions.
-/
import Lean.Compiler.LCNF.Passes

namespace Lean4LeanCompiler.LCNFExperimental

open Lean
open Lean.Compiler.LCNF

mutual
  partial def eraseZeroRC (code : Code .impure) : Code .impure :=
    match code with
    | .let d k => .let d (eraseZeroRC k)
    | .jp (.mk x binder params ty body) k =>
      .jp (.mk x binder params ty (eraseZeroRC body)) (eraseZeroRC k)
    | .cases (.mk ty result discr alts) =>
      .cases (.mk ty result discr (alts.map eraseZeroRCAlt))
    | .oset x i y k h => .oset x i y (eraseZeroRC k) h
    | .uset x i y k h => .uset x i y (eraseZeroRC k) h
    | .sset x i offset y ty k h => .sset x i offset y ty (eraseZeroRC k) h
    | .setTag x i k h => .setTag x i (eraseZeroRC k) h
    | .del x k h => .del x (eraseZeroRC k) h
    | .inc x n checked persistent k h =>
      if n = 0 then eraseZeroRC k
      else .inc x n checked persistent (eraseZeroRC k) h
    | .dec x n checked persistent objs? k h =>
      if n = 0 then eraseZeroRC k
      else .dec x n checked persistent objs? (eraseZeroRC k) h
    | other => other

  partial def eraseZeroRCAlt (alt : Alt .impure) : Alt .impure :=
    match alt with
    | .ctorAlt info body h => .ctorAlt info (eraseZeroRC body) h
    | .default body => .default (eraseZeroRC body)
    | other => other
end

/-- In particular, do not silently rewrite the kernel checker. -/
def experimentalPrefix : String := "Lean4LeanCompiler.Examples."

def optDecl (decl : Decl .impure) : Decl .impure := Id.run do
  unless decl.name.toString.startsWith experimentalPrefix do
    return decl
  match decl.value with
  | .code body => return { decl with value := .code (eraseZeroRC body) }
  | _ => return decl

def zeroRcPass : Pass where
  phase := .impure
  phaseOut := .impure
  name := Name.mkSimple "l4lcElideZeroRC"
  run := fun decls => do
    let mut result := #[]
    for decl in decls do
      let next := optDecl decl
      if decl.name.toString.startsWith experimentalPrefix then
        logInfo m!"[l4lc] {decl.name}: {decl.size} -> {next.size} nodes; stock backend; certified=false"
      result := result.push next
    return result

/-- Pinned upstream Lean pass name is coalesceRc. -/
@[cpass] meta def installZeroRc : PassInstaller :=
  PassInstaller.installBefore .impure (Name.mkSimple "coalesceRc") (fun _ => zeroRcPass)

end Lean4LeanCompiler.LCNFExperimental
