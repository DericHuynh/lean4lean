/-
Conservative structural inventory on real, post-elaboration impure LCNF.
Each count is a STATIC syntactic site count across all branches; it is NOT
a dynamic allocation count, bound on execution, or safety certificate.
Unknown operations and calls remain unvalidated.
-/
import Lean.Compiler.LCNF.Passes

namespace Lean4LeanCompiler.LCNFInventory

open Lean
open Lean.Compiler.LCNF

structure Sites where
  ctor : Nat := 0
  reset : Nat := 0
  reuse : Nat := 0
  calls : Nat := 0
  closures : Nat := 0
  mutation : Nat := 0
  inc : Nat := 0
  dec : Nat := 0
  checks : Nat := 0
  branches : Nat := 0
  jumps : Nat := 0
  unknown : Nat := 0
  deriving Inhabited

def Sites.add (a b : Sites) : Sites :=
  { ctor := a.ctor + b.ctor
    reset := a.reset + b.reset
    reuse := a.reuse + b.reuse
    calls := a.calls + b.calls
    closures := a.closures + b.closures
    mutation := a.mutation + b.mutation
    inc := a.inc + b.inc
    dec := a.dec + b.dec
    checks := a.checks + b.checks
    branches := a.branches + b.branches
    jumps := a.jumps + b.jumps
    unknown := a.unknown + b.unknown }

def Sites.render (s : Sites) : String :=
  s!"ctors={s.ctor}, resets={s.reset}, reuses={s.reuse}, calls={s.calls}, closures={s.closures}, mutations={s.mutation}, RC=({s.inc},{s.dec}), uniquenessChecks={s.checks}, branches={s.branches}, jumps={s.jumps}, unknown={s.unknown}"

/-- An unknown or external call is NOT assigned a pure or allocation-free
    semantic interpretation. This inventory has no checker acceptance bit. -/
def valueSites : LetValue .impure → Sites
  | .ctor .. => { ctor := 1 }
  | .reset .. => { reset := 1 }
  | .reuse .. => { reuse := 1 }
  | .fap .. => { calls := 1 }
  | .pap .. => { closures := 1, unknown := 1 }
  | .fvar .. => { calls := 1, unknown := 1 }
  | .isShared .. => { checks := 1 }
  | .box .. => { unknown := 1 }
  | .unbox .. => { unknown := 1 }
  | _ => {}

mutual
  partial def codeSites (c : Code .impure) : Sites :=
    match c with
    | .let decl k => (valueSites decl.value).add (codeSites k)
    | .jp (.mk _ _ _ _ body) k => (codeSites body).add (codeSites k)
    | .cases (.mk _ _ _ alts) =>
      alts.foldl (fun acc alt => acc.add (altSites alt)) { branches := 1 }
    | .oset _ _ _ k _ | .uset _ _ _ k _ =>
      { (codeSites k) with mutation := (codeSites k).mutation + 1 }
    | .sset _ _ _ _ _ k _ =>
      { (codeSites k) with mutation := (codeSites k).mutation + 1 }
    | .setTag _ _ k _ =>
      { (codeSites k) with mutation := (codeSites k).mutation + 1 }
    | .del _ k _ => codeSites k
    | .inc _ _ _ _ k _ =>
      { (codeSites k) with inc := (codeSites k).inc + 1 }
    | .dec _ _ _ _ _ k _ =>
      { (codeSites k) with dec := (codeSites k).dec + 1 }
    | .jmp .. => { jumps := 1 }
    | .return .. | .unreach .. => {}
    | _ => { unknown := 1 }

  partial def altSites (alt : Alt .impure) : Sites :=
    match alt with
    | .ctorAlt _ body _ => codeSites body
    | .default body => codeSites body
    | _ => { unknown := 1 }
end

/-- Executes over a small synthetic IR fragment to test the inventory code.
    The full frontend path is exercised by the separate Examples module. -/
def inventorySmoke : IO Unit := do
  let x : FVarId := ⟨Name.mkSimple "inv_x"⟩
  let code : Code .impure :=
    .inc x 1 false false (.dec x 1 false false none (.return x))
  let s := codeSites code
  unless s.inc == 1 && s.dec == 1 && s.ctor == 0 && s.calls == 0 do
    throw <| IO.userError "LCNF structural inventory mismatch"

end Lean4LeanCompiler.LCNFInventory
