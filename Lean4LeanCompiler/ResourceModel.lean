/-
A small, executable byte-storage semantics written entirely in Lean 4.
It is NOT a model of the full Lean heap/ABI. A Source is flat (has no
reference-typed descendants). Fresh allocation assumes disjointness;
unique=true is a precondition, not a proof of runtime uniqueness.
-/
import Init.Omega

namespace Lean4LeanCompiler.ResourceModel

inductive Source where
  | live (bytes : List UInt8) (borrows : Nat) (unique : Bool)
  | dropped

inductive Destination where
  | absent
  | building (capacity : Nat) (bytes : List UInt8) (within : bytes.length ≤ capacity)
  | published (capacity : Nat) (bytes : List UInt8) (full : bytes.length = capacity)

structure Cost where
  totalAllocations : Nat := 0
  totalBytesAllocated : Nat := 0
  regionAllocations : Nat := 0
  regionBytesAllocated : Nat := 0
  reuseCount : Nat := 0
  deriving Inhabited, DecidableEq

structure State where
  source : Source
  -- Saved unboxed UInt8 registers; no pointer identity is modeled.
  registers : List (Nat × UInt8) := []
  dest : Destination := .absent
  separate : Bool := false
  insideRegion : Bool := false
  regionOpened : Bool := false
  regionClosed : Bool := false
  cost : Cost := {}

inductive Op where
  | fresh (capacity : Nat)
  | beginRegion
  | endRegion
  | borrow
  | release
  | load (index register : Nat)
  | copy (index : Nat)
  | append (value : UInt8)
  | appendRegister (register : Nat)
  | publish
  | dropSource
  | reuseSource (capacity : Nat)
  | nop
  | unsupported
  deriving DecidableEq

/-- Destination writes preserve the initialized-prefix invariant. -/
def Destination.append? (d : Destination) (value : UInt8) : Option Destination :=
  match d with
  | .building capacity bytes _ =>
    if h : bytes.length < capacity then
      some (.building capacity (bytes ++ [value]) (by simp; omega))
    else none
  | _ => none

/-- Only a fully initialized destination may become observable. -/
def Destination.publish? (d : Destination) : Option Destination :=
  match d with
  | .building capacity bytes _ =>
    if h : bytes.length = capacity then
      some (.published capacity bytes h)
    else none
  | _ => none

def Destination.result? : Destination → Option (List UInt8)
  | .published _ bytes _ => some bytes
  | _ => none

def Destination.isPublished : Destination → Bool
  | .published .. => true
  | _ => false

def Source.borrowCount : Source → Nat
  | .live _ n _ => n
  | .dropped => 0

def State.result? (s : State) : Option (List UInt8) := s.dest.result?

/-- Each rejected precondition results in none. There is no silent stock
    fallback, implicit allocation, unchecked write or borrowing escape. -/
def step (s : State) : Op → Option State
  | .fresh n =>
      match s.dest with
      | .absent =>
        let c := { s.cost with
          totalAllocations := s.cost.totalAllocations + 1
          totalBytesAllocated := s.cost.totalBytesAllocated + n
          regionAllocations := s.cost.regionAllocations + (if s.insideRegion then 1 else 0)
          regionBytesAllocated := s.cost.regionBytesAllocated + (if s.insideRegion then n else 0) }
        some { s with dest := .building n [] (by simp), separate := true, cost := c }
      | _ => none
  | .beginRegion =>
      if !s.regionOpened && !s.insideRegion then
        some { s with insideRegion := true, regionOpened := true }
      else none
  | .endRegion =>
      if s.insideRegion && !s.regionClosed then
        some { s with insideRegion := false, regionClosed := true }
      else none
  | .borrow =>
      match s.source with
      | .live bs count unique =>
          some { s with source := .live bs (count + 1) unique }
      | .dropped => none
  | .release =>
      match s.source with
      | .live bs count unique =>
          if count > 0 then
            some { s with source := .live bs (count - 1) unique }
          else none
      | .dropped => none
  | .load index register =>
      match s.source with
      | .live bs count _ =>
          if count > 0 then
            if s.registers.any (fun p => p.1 == register) then none
            else
              match bs[index]? with
              | some value => some { s with registers := (register, value) :: s.registers }
              | none => none
          else none
      | .dropped => none
  | .copy index =>
      if s.separate then
        match s.source with
        | .live bs count _ =>
            if count > 0 then
              match bs[index]? with
              | some value => do
                  let dest ← s.dest.append? value
                  some { s with dest }
              | none => none
            else none
        | .dropped => none
      else none
  | .append value =>
      if s.separate then do
        let dest ← s.dest.append? value
        some { s with dest }
      else none
  | .appendRegister register =>
      if s.separate then
        match s.registers.find? (fun p => p.1 == register) with
        | none => none
        | some (_, value) => do
            let dest ← s.dest.append? value
            some { s with dest }
      else none
  | .publish => do
      let dest ← s.dest.publish?
      some { s with dest }
  | .dropSource =>
      match s.source with
      | .live _ 0 _ => some { s with source := .dropped }
      | _ => none
  | .reuseSource capacity =>
      match s.dest, s.source with
      | .absent, .live bs 0 true =>
          if capacity ≤ bs.length then
            some { s with
              source := .dropped
              dest := .building capacity [] (by simp)
              separate := true
              cost := { s.cost with reuseCount := s.cost.reuseCount + 1 } }
          else none
      | _, _ => none
  | .nop => some s
  | .unsupported => none

/-- The terminating operational fragment. Rejection is different from
    termination/divergence of arbitrary Lean programs. -/
def run : List Op → State → Option State
  | [], s => some s
  | op :: ops, s => do
    let next ← step s op
    run ops next

structure Budget where
  maxRegionAllocations : Nat
  maxRegionBytes : Nat

def MeetsContract (budget : Budget) (s : State) : Prop :=
  s.regionOpened = true ∧ s.regionClosed = true ∧ s.insideRegion = false ∧
  s.source.borrowCount = 0 ∧ s.dest.isPublished = true ∧
  s.cost.regionAllocations ≤ budget.maxRegionAllocations ∧
  s.cost.regionBytesAllocated ≤ budget.maxRegionBytes

instance (budget : Budget) (s : State) : Decidable (MeetsContract budget s) := by
  unfold MeetsContract
  infer_instance

/-- The accepted certificate is the exact list of modeled instructions,
    exact initial state and budget. No runtime bytes are certified yet. -/
def check (budget : Budget) (ops : List Op) (initial : State) : Bool :=
  match run ops initial with
  | none => false
  | some final => decide (MeetsContract budget final)

/-- The checker can accept only an actual final model state satisfying
    precisely the advertised contract. -/
theorem check_sound (budget : Budget) (ops : List Op) (initial : State)
    (h : check budget ops initial = true) :
    ∃ final, run ops initial = some final ∧ MeetsContract budget final := by
  unfold check at h
  cases hrun : run ops initial with
  | none => simp [hrun] at h
  | some final =>
    refine ⟨final, rfl, ?_⟩
    have hd : decide (MeetsContract budget final) = true := by
      simpa [hrun] using h
    exact of_decide_eq_true hd

/-- Removing model no-ops preserves every modeled effect, failure and cost. -/
def eraseNops : List Op → List Op
  | [] => []
  | op :: ops => if op = .nop then eraseNops ops else op :: eraseNops ops

theorem run_eraseNops (ops : List Op) (initial : State) :
    run (eraseNops ops) initial = run ops initial := by
  induction ops generalizing initial with
  | nil => rfl
  | cons op ops ih =>
    by_cases hop : op = .nop
    · subst op
      simpa [eraseNops, run, step] using ih initial
    · simp only [eraseNops, if_neg hop]
      simp only [run]
      cases hstep : step initial op with
      | none => simp
      | some next => simpa [hstep] using ih next

theorem check_eraseNops (budget : Budget) (ops : List Op) (initial : State) :
    check budget (eraseNops ops) initial = check budget ops initial := by
  simp [check, run_eraseNops]

/-- Copy allocates the final output before the writer's metered region. -/
def copyFour : List Op :=
  [.fresh 4, .beginRegion, .borrow, .copy 0, .copy 1, .copy 2, .copy 3,
   .release, .publish, .endRegion]

/-- Load all scalar input bytes before consuming unique flat source storage. -/
def reverseFourReuse : List Op :=
  [.beginRegion, .borrow, .load 0 0, .load 1 1, .load 2 2, .load 3 3,
   .release, .reuseSource 4, .appendRegister 3, .appendRegister 2,
   .appendRegister 1, .appendRegister 0, .publish, .endRegion]

def flatSource (bytes : List UInt8) (unique : Bool := false) : State :=
  { source := .live bytes 0 unique }

def noAllocation : Budget := ⟨0, 0⟩

end Lean4LeanCompiler.ResourceModel
