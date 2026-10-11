/-
A closed, fail-closed importer of the actual, stock-compiled impure-LCNF
pattern for a two-argument UInt64 addition. It does not treat arbitrary
calls, recursion, branches or effects as equivalent to addition.
-/
import Lean.Compiler.LCNF.Passes
import Lean4LeanCompiler.Native.ISA

namespace Lean4LeanCompiler.Native.FromLCNFArithmetic
open Lean Lean.Compiler.LCNF

inductive Operation where
  | add
  deriving Inhabited, BEq, DecidableEq, Repr

/-- LEA rax,[rdi+rsi]; RET, with modular UInt64 arithmetic. -/
def encode : Operation → List UInt8
  | .add => Lean4LeanCompiler.Native.ISA.addCode

def decode (bytes : List UInt8) : Option Operation :=
  if bytes == encode .add then some .add else none

theorem decode_encode (op : Operation) :
    decode (encode op) = some op := by
  cases op <;> decide

def eval : Operation → UInt64 → UInt64 → UInt64
  | .add, a, b => a + b

theorem eval_add (a b : UInt64) : eval .add a b = a + b := rfl

/-- Full-function pattern: exactly two distinct UInt64 arguments, one
    binding that directly calls the specifically allowed UInt64.add
    primitive using these arguments in order, and returns that binding.
    The stock compiler may erase/transform other code, which is why we
    impose exact form and separately check source equality in Lean. -/
def recognize (d : Decl .impure) : Option Operation := do
  if !d.safe || d.recursive || !d.levelParams.isEmpty ||
      d.type != ImpureType.uint64 then
    none
  else
    match d.params.toList, d.value with
    | [p, q], .code (.let bind (.return x)) =>
      if p.type != ImpureType.uint64 || q.type != ImpureType.uint64 ||
          p.borrow || q.borrow || p.fvarId == q.fvarId ||
          bind.fvarId != x || bind.type != ImpureType.uint64 then
        none
      else
        match bind.value with
        | .fap fn args =>
          match args.toList with
          | [.fvar a, .fvar b] =>
            if fn.toString == "UInt64.add" &&
                a == p.fvarId && b == q.fvarId then
              some .add
            else none
          | _ => none
        | _ => none
    | _, _ => none

/-- Negative IR fixtures prove that unsupported opcodes do not decode as
    this operation. A full operational source/LCNF proof still requires
    a semantics for arbitrary LCNF and stock primitive erasure. -/
example : decode [0xc3] = none := by decide

#print axioms decode_encode
#print axioms eval_add

end Lean4LeanCompiler.Native.FromLCNFArithmetic
