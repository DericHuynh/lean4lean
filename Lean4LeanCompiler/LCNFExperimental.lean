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
def isTarget (n : Name) : Bool :=
  let name := n.toString
  name == "Lean4LeanCompiler.Examples.copyFour" ||
  name == "Lean4LeanCompiler.Examples.reverseFour" ||
  name == "Lean4LeanCompiler.Examples.writeFourInto" ||
  name == "Lean4LeanCompiler.Examples.bumpList"

def optDecl (decl : Decl .impure) : Decl .impure := Id.run do
  unless isTarget decl.name do
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
      if isTarget decl.name then
        logInfo m!"[l4lc] {decl.name}: {decl.size} -> {next.size} nodes; stock backend; certified=false"
      result := result.push next
    return result

/-- Executable unit test of the actual LCNF rewrite on synthetic IR.
    Its success is not a proof of source-language or runtime correctness. -/
def rcPassSmoke : IO Unit := do
  let x : FVarId := ⟨Name.mkSimple "rc_test"⟩
  let zero : Code .impure := .inc x 0 false false (.return x)
  let positive : Code .impure := .inc x 1 false false (.return x)
  let nested : Code .impure :=
    .inc x 0 false false (.dec x 0 false false none (.inc x 1 false false (.return x)))
  unless (eraseZeroRC zero).size == 0 do
    throw <| IO.userError "zero inc was not removed"
  unless (eraseZeroRC positive).size == 1 do
    throw <| IO.userError "positive inc was incorrectly removed"
  unless (eraseZeroRC nested).size == 1 do
    throw <| IO.userError "nested zero RC instructions were not removed"

/-- Pinned upstream Lean pass name is coalesceRc. -/
@[cpass] meta def installZeroRc : PassInstaller :=
  PassInstaller.installBefore .impure (Name.mkSimple "coalesceRc") (fun _ => zeroRcPass)

end Lean4LeanCompiler.LCNFExperimental
