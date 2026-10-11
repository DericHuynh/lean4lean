import Lean4LeanCompiler.MorphicModeProbe

set_option trace.Compiler.morphicBorrow true

namespace Lean4LeanCompiler.MorphicModeExamples

structure Box where
  value : List UInt8
  deriving BEq

@[noinline] def wrap (xs : List UInt8) : Box := ⟨xs⟩

@[noinline] def readOnly (xs : List UInt8) : Nat := xs.length

@[noinline] def consume (xs : List UInt8) : List UInt8 := xs

@[noinline] def wrapTwice (xs : List UInt8) : Box × Box :=
  (wrap xs, wrap xs)

def smoke : IO Unit := do
  for n in [0, 1, 3, 64, 256] do
    let xs := (List.range n).map (fun i => (i % 251).toUInt8)
    let (left, right) := wrapTwice xs
    unless left.value == xs && right.value == xs && readOnly xs == n do
      throw <| IO.userError "Morphic borrow alias test failed"
  IO.println "Morphic mode probe passed"

end Lean4LeanCompiler.MorphicModeExamples

def main : IO Unit := Lean4LeanCompiler.MorphicModeExamples.smoke
