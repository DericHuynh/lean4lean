/-
Copyright (c) 2026 Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

prelude
public import Lean.Compiler.LCNF.Basic

public section

namespace Lean.Compiler.LCNF.MorphicBorrow.DirectTransfer

private def argUses (x : FVarId) : Arg .impure → Bool
  | .fvar y => y == x
  | _ => false

private def argsUse (x : FVarId) (args : Array (Arg .impure)) : Bool :=
  args.any (argUses x)

/-- Independently reject known operations that consume, move, or expose the
    original owner. Constructors and direct calls remain candidates: the
    normal mode solver and stock RC insertion must justify them separately.
    This checker does not certify nested heap aliases or native semantics. -/
def dangerousValue (x : FVarId) : LetValue .impure → Bool
  | .reset _ y => x == y
  | .reuse y _ _ args => x == y || argsUse x args
  | .oproj _ y => x == y
  | .uproj _ y => x == y
  | .sproj _ _ y => x == y
  | .box _ y => x == y
  | .fvar y args => x == y || argsUse x args
  | .pap _ args => argsUse x args
  | .ctor .. | .fap .. | .lit .. | .erased | .unbox .. | .isShared .. => false
  | _ => true

/-- A total fuel-bounded scan of actual impure LCNF. Exhaustion rejects
    the proposed borrowed mode instead of inventing an ownership proof. -/
def hasDirectTransferAux : Nat → FVarId → Code .impure → Bool
  | 0, _, _ => true
  | fuel + 1, x, code =>
    match code with
    | .let decl k =>
      dangerousValue x decl.value || hasDirectTransferAux fuel x k
    | .jp (.mk _ _ _ _ body) k =>
      hasDirectTransferAux fuel x body || hasDirectTransferAux fuel x k
    | .cases (.mk _ _ _ alts) =>
      alts.any (fun alt => hasDirectTransferAux fuel x alt.getCode)
    | .jmp _ args => argsUse x args
    | .return y => x == y
    | .unreach .. => false
    | .oset y _ arg k _ =>
      x == y || argUses x arg || hasDirectTransferAux fuel x k
    | .uset y _ z k _ | .sset y _ _ z _ k _ =>
      x == y || x == z || hasDirectTransferAux fuel x k
    | .setTag y _ k _ | .del y k _ =>
      x == y || hasDirectTransferAux fuel x k
    | .inc y _ _ _ k _ | .dec y _ _ _ _ k _ =>
      x == y || hasDirectTransferAux fuel x k

def validate (x : FVarId) (code : Code .impure) : Bool :=
  !hasDirectTransferAux (code.size + 1) x code

def NoDirectTransfer (x : FVarId) (code : Code .impure) : Prop :=
  hasDirectTransferAux (code.size + 1) x code = false

/-- Acceptance is evidence about this *actual* LCNF syntax, not a lifetime
    or physical heap theorem. -/
theorem validate_sound (x : FVarId) (code : Code .impure)
    (h : validate x code = true) : NoDirectTransfer x code := by
  unfold validate NoDirectTransfer at *
  cases hx : hasDirectTransferAux (code.size + 1) x code <;>
    simp [hx] at h ⊢

/-- Fuel zero conservatively rejects even a syntactically harmless path. -/
private def x : FVarId := ⟨Name.mkSimple "source"⟩
private def y : FVarId := ⟨Name.mkSimple "result"⟩

example : hasDirectTransferAux 4 x (.return x) = true := by decide
example : hasDirectTransferAux 4 x (.return y) = false := by decide
example : hasDirectTransferAux 0 x (.return y) = true := by decide

private def cinfo : CtorInfo :=
  { name := Name.mkSimple "Box.mk"
    cidx := 0, size := 1, usize := 0, ssize := 0 }

private def boxCode : Code .impure :=
  .let { fvarId := y, binderName := Name.mkSimple "result",
         type := ImpureType.object,
         value := .ctor cinfo #[.fvar x] } (.return y)

example : hasDirectTransferAux 4 x boxCode = false := by decide

private def resetCode : Code .impure :=
  .let { fvarId := y, binderName := Name.mkSimple "reset",
         type := ImpureType.tobject,
         value := .reset 1 x } (.return y)

example : hasDirectTransferAux 4 x resetCode = true := by decide

private def closureCode : Code .impure :=
  .let { fvarId := y, binderName := Name.mkSimple "closure",
         type := ImpureType.object,
         value := .pap (Name.mkSimple "f") #[.fvar x] } (.return y)

example : hasDirectTransferAux 4 x closureCode = true := by decide

private def aliasCode : Code .impure :=
  .let { fvarId := y, binderName := Name.mkSimple "projection",
         type := ImpureType.object,
         value := .oproj 0 x } (.return y)

example : hasDirectTransferAux 4 x aliasCode = true := by decide

#print axioms validate_sound

end Lean.Compiler.LCNF.MorphicBorrow.DirectTransfer
