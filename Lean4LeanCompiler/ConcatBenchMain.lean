/-
Reproducible comparison of stock-compiled versus @[csimp]-selected
three-segment byte joining in actual Lean-generated native executables.
Both implementations have the same Lean source semantics and run under
the same optimization mode and hardware.

Times are observations, NOT guaranteed performance theorems.
-/
import Lean4LeanCompiler.VerifiedJoin

namespace Lean4LeanCompiler.ConcatBench
open Lean4LeanCompiler

def mkVariants (n : Nat) : Array ByteArray := Id.run do
  let mut arr := #[]
  for k in [:16] do
    arr := arr.push ((List.replicate n k.toUInt8).toByteArray)
  return arr

/-- Apply a compiled function pointer to changing inputs and consume
    observable bytes so the computation cannot be optimized away. -/
def timed
    (f : ByteArray → ByteArray → ByteArray → ByteArray)
    (variants : Array ByteArray) (b c : ByteArray) (iterations : Nat) :
    IO (Nat × Nat) := do
  let start ← IO.monoNanosNow
  let mut checksum : Nat := 0
  for i in [:iterations] do
    let a := variants[i % variants.size]!
    let out := f a b c
    checksum := checksum + out.size + (out.get! (i % out.size)).toNat
  let finish ← IO.monoNanosNow
  return ((finish - start).toNat, checksum)

def benchmark : IO Unit := do
  for n in [256, 4096, 16384] do
    let xs := mkVariants n
    let b := ((List.replicate n (0x55 : UInt8)).toByteArray)
    let c := ((List.replicate n (0xa9 : UInt8)).toByteArray)
    let stock := Reference.join3Baseline xs[0]! b c
    let optimized := VerifiedJoin.join3Optimized xs[0]! b c
    unless stock == optimized do
      throw <| IO.userError "csimp-optimized join mismatch"
    let iterations := if n == 16384 then 1500 else 6000
    -- Same benchmark function, same data, same repetitions. ABBA alternation
    -- avoids systematically rewarding the second/hot implementation.
    for rep in [:5] do
      let mut baseline : Nat := 0
      let mut fast : Nat := 0
      let mut baselineChecksum : Nat := 0
      let mut fastChecksum : Nat := 0
      if rep % 2 == 0 then
        let (t1, c1) ← timed Reference.join3Baseline xs b c iterations
        baseline := t1
        baselineChecksum := c1
        let (t2, c2) ← timed VerifiedJoin.join3Optimized xs b c iterations
        fast := t2
        fastChecksum := c2
      else
        let (t1, c1) ← timed VerifiedJoin.join3Optimized xs b c iterations
        fast := t1
        fastChecksum := c1
        let (t2, c2) ← timed Reference.join3Baseline xs b c iterations
        baseline := t2
        baselineChecksum := c2
      unless baselineChecksum == fastChecksum do
        throw <| IO.userError "benchmark results differ"
      let ratio := fast.toFloat / baseline.toFloat
      IO.println s!"lean-concat-bench size={n} repetitions={iterations} rep={rep} stockNs={baseline} verifiedFastNs={fast} ratio={ratio} checksum={baselineChecksum}"
  IO.println "NB: microbenchmark of compiled Lean serialization; not a full Lean compiler bootstrap benchmark"

end Lean4LeanCompiler.ConcatBench

def main : IO Unit := Lean4LeanCompiler.ConcatBench.benchmark
