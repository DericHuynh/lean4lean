/-
Conservative proof-producing *syntactic* resource gate on actual Lean
impure-LCNF declarations. It rejects arbitrary calls, constructors, RC,
mutation, branches, closures and unknown instructions. Acceptance is
proven to imply zero listed static sites -- NOT zero physical allocation.

Before a true resource certificate is issued, a verified correspondence
between LCNF, runtime primitives and machine semantics is still required.
-/
import Lean4LeanCompiler.LCNFInventory

namespace Lean4LeanCompiler.LCNFStrict
open Lean
open Lean.Compiler.LCNF
open Lean4LeanCompiler.LCNFInventory

/-- Every site with presently unknown allocation/lifetime effects is
    rejected. Even direct primitive calls are rejected until summarized. -/
def NoUncheckedSites (s : Sites) : Prop :=
  s.ctor = 0 ∧ s.reset = 0 ∧ s.reuse = 0 ∧
  s.calls = 0 ∧ s.closures = 0 ∧ s.mutation = 0 ∧
  s.inc = 0 ∧ s.dec = 0 ∧ s.checks = 0 ∧
  s.branches = 0 ∧ s.jumps = 0 ∧ s.unknown = 0

instance (s : Sites) : Decidable (NoUncheckedSites s) := by
  unfold NoUncheckedSites
  infer_instance

/-- A post-elaboration, impure-LCNF declaration is accepted only when it
    is a safe, nonrecursive code declaration with no unchecked static
    resource/effect sites. This is *not* an ABI or heap theorem. -/
def check (d : Decl .impure) : Bool :=
  match d.value with
  | .code code =>
    decide (d.safe = true ∧ d.recursive = false ∧ NoUncheckedSites (codeSites code))
  | .extern .. => false

theorem check_sound (d : Decl .impure) (h : check d = true) :
    ∃ code, d.value = .code code ∧ d.safe = true ∧
      d.recursive = false ∧ NoUncheckedSites (codeSites code) := by
  unfold check at h
  cases hval : d.value with
  | extern _ => simp [hval] at h
  | code body =>
      refine ⟨body, rfl, ?_⟩
      exact of_decide_eq_true (by simpa [hval] using h)

/-- Strict mode does not silently use stock fallback. -/
def validate (d : Decl .impure) : Except String Unit :=
  if check d then
    .ok ()
  else
    .error s!"not strict-resource supported: {d.name} (arbitrary call/heap/alias effects rejected)"

/-- This profile is an explicit resource gate, not a dynamic byte counter. -/
def gatePass : Pass where
  phase := .impure
  phaseOut := .impure
  name := Name.mkSimple "l4lcResourceGate"
  run := fun decls => do
    for decl in decls do
      if decl.name.toString.startsWith "Lean4LeanCompiler.StrictExamples." then
        let verdict := validate decl
        match verdict with
        | .ok _ =>
          logInfo m!"[l4lc-gate] {decl.name}: staticSitesAccepted=true, nativeCertificate=false"
        | .error msg =>
          logInfo m!"[l4lc-gate] {decl.name}: staticSitesAccepted=false, nativeCertificate=false, reason={msg}"
    return decls

@[cpass] meta def installGate : PassInstaller :=
  PassInstaller.installAfter .impure (Name.mkSimple "coalesceRc") (fun _ => gatePass)

/-- Synthetic IR unit test with a genuinely bound input parameter.
    This checks the syntactic policy, not source correctness. -/
def gateSmoke : IO Unit := do
  let x : FVarId := ⟨Name.mkSimple "x"⟩
  let good : Decl .impure :=
    { name := Name.mkSimple "id"
      levelParams := []
      type := ImpureType.uint64
      params := #[{ fvarId := x, binderName := Name.mkSimple "x",
                    type := ImpureType.uint64, borrow := false }]
      value := .code (.return x)
      inlineAttr? := none }
  unless check good do
    throw <| IO.userError "strict gate rejected an effect-free identity"
  unless (validate good).isOk do
    throw <| IO.userError "strict gate returned fallback for accepted program"
  let bad : Decl .impure :=
    { good with value := .code (.inc x 1 false false (.return x)) }
  if check bad then
    throw <| IO.userError "strict gate accepted explicit RC"
  if (validate bad).isOk then
    throw <| IO.userError "strict gate allowed an RC fallback"
  let unreachable := { good with value := .code (.unreach ImpureType.uint64) }
  if check unreachable then
    throw <| IO.userError "strict gate accepted unreachable/faulting code"

#print axioms check_sound

end Lean4LeanCompiler.LCNFStrict
