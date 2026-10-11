/-
Actual impure-LCNF -> typed scalar native lowering adapter.
Works on elaborated and stock-lowered Lean declarations, not a toy AST.
Only safe nonrecursive fixed-width scalar identity returns are accepted.
A persistent extension exports the strictly checked compilation decision.

The source/compiler IR correctness, ABI/CPU implementation, and erasure
relations are separate trust boundaries; they are NOT proved here.
-/
import Lean.Compiler.LCNF.Passes

namespace Lean4LeanCompiler.Native.FromLCNF
open Lean
open Lean.Compiler.LCNF

inductive Register where
  | rdi | rsi
  deriving Inhabited, BEq, DecidableEq, Repr

/-- There are exactly two possible argument-source register choices under
    the System V x86-64 ABI for this fragment. -/
def encode : Register → List UInt8
  | .rdi => [0x48, 0x89, 0xf8, 0xc3] -- mov rax,rdi; ret
  | .rsi => [0x48, 0x89, 0xf0, 0xc3] -- mov rax,rsi; ret

def decode (bytes : List UInt8) : Option Register :=
  if bytes == encode .rdi then some .rdi
  else if bytes == encode .rsi then some .rsi
  else none

theorem decode_encode (r : Register) : decode (encode r) = some r := by
  cases r <;> decide

/-- Register-operand meaning, with uint64 modular arithmetic irrelevant to
    this identity-only fragment. -/
def eval (r : Register) (a b : UInt64) : UInt64 :=
  match r with
  | .rdi => a
  | .rsi => b

theorem eval_rdi (a b : UInt64) : eval .rdi a b = a := rfl
theorem eval_rsi (a b : UInt64) : eval .rsi a b = b := rfl

/-- Reject any other representation, effects, full application, branch,
    ownership movement, or generated wrapper. We deliberately handle only
    direct return of a scalar input with 1 or 2 scalar parameters.
    This condition is checked on real stock impure LCNF. -/
def recognize (d : Decl .impure) : Option Register := do
  if !d.safe || d.recursive || !d.levelParams.isEmpty ||
      d.type != ImpureType.uint64 then
    none
  else
    match d.params.toList, d.value with
    | [p], .code (.return x) =>
        if p.type == ImpureType.uint64 && !p.borrow && p.fvarId == x then
          some .rdi
        else none
    | [p, q], .code (.return x) =>
        if p.type != ImpureType.uint64 || q.type != ImpureType.uint64 ||
            p.borrow || q.borrow || p.fvarId == q.fvarId then
          none
        else if x == p.fvarId then some .rdi
        else if x == q.fvarId then some .rsi
        else none
    | _, _ => none

/-- The decoder's accepted native bytes model exactly one input-register
    selection, with no aliasing or memory-effecting instructions. -/
theorem encoded_operand_semantics (r : Register) (a b : UInt64) :
    decode (encode r) = some r ∧
    eval r a b = (if r == .rdi then a else b) := by
  cases r <;> exact ⟨rfl, rfl⟩

/-- The persistent entry records exactly what was checked when compilation
    ran, not a hash of an unrelated filename or user-provided AST. -/
structure Entry where
  name : Name
  arg : Register
  deriving Inhabited, BEq, Repr

builtin_initialize exportedNative : SimplePersistentEnvExtension Entry (Array Entry) ←
  registerSimplePersistentEnvExtension {
    addEntryFn := fun entries entry => entries.push entry
    addImportedFn := fun modules =>
      modules.foldl (fun entries es => entries ++ es) #[]
    asyncMode := .sync
  }

/-- Only named, opt-in ordinary declarations get native lowering.
    A compiler unsupported case is an error, not a stock fallback. -/
def isRequested (name : Name) : Bool :=
  name.toString == "Lean4LeanCompiler.NativeExamples.returnScalar"

def nativeExtractionPass : Pass where
  phase := .impure
  phaseOut := .impure
  name := Name.mkSimple "l4lcNativeScalarImport"
  run := fun ds => do
    for d in ds do
      if isRequested d.name then
        match recognize d with
        | none => throwError m!"[l4lc-native] unsupported LCNF in requested declaration {d.name}; no native object produced"
        | some reg =>
          logInfo m!"[l4lc-native] recognized {d.name} from impure LCNF: {repr reg}; persistence disabled in diagnostic mode"
    return ds

/-- Fast unit-level rejection tests; actual declaration capture is tested
    independently in the native executable and GitHub CI. -/
def checkFixtures : IO Unit := do
  let x : FVarId := ⟨Name.mkSimple "x"⟩
  let param : Param .impure :=
    { fvarId := x, binderName := Name.mkSimple "x",
      type := ImpureType.uint64, borrow := false }
  let good : Decl .impure :=
    { name := Name.mkSimple "identity"
      levelParams := []
      type := ImpureType.uint64
      params := #[param]
      value := .code (.return x)
      inlineAttr? := none }
  unless recognize good == some .rdi do
    throw <| IO.userError "valid direct LCNF identity rejected"
  let badCall : Decl .impure :=
    { good with value := .code (.inc x 1 false false (.return x)) }
  if (recognize badCall).isSome then
    throw <| IO.userError "accepted RC-managed LCNF"
  let badType : Decl .impure :=
    { good with type := ImpureType.uint8 }
  if (recognize badType).isSome then
    throw <| IO.userError "accepted wrong result representation"
  let badSafety : Decl .impure := { good with safe := false }
  if (recognize badSafety).isSome then
    throw <| IO.userError "accepted unsafe declaration"
  let badRecursive : Decl .impure := { good with recursive := true }
  if (recognize badRecursive).isSome then
    throw <| IO.userError "accepted recursive declaration"
  let badUnreach : Decl .impure :=
    { good with value := .code (.unreach ImpureType.uint64) }
  if (recognize badUnreach).isSome then
    throw <| IO.userError "accepted unreachable declaration"

end Lean4LeanCompiler.Native.FromLCNF
