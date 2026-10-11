import Lean4LeanCompiler.AppendProbeStock
import Lean4LeanCompiler.AppendProbeOptimized

namespace Lean4LeanCompiler.AppendProbeBenchmark

def variants (n : Nat) : Array ByteArray := Id.run do
  let mut out := #[]
  for i in [:16] do
    out := out.push (List.replicate n i.toUInt8).toByteArray
  return out

def timed (f : ByteArray → ByteArray → ByteArray → ByteArray)
    (xs : Array ByteArray) (b c : ByteArray) (iters : Nat) :
    IO (Nat × Nat) := do
  let begin ← IO.monoNanosNow
  let mut checksum := 0
  for i in [:iters] do
    let a := xs[i % xs.size]!
    let x := f a b c
    checksum := checksum + x.size + (x.get! (i % x.size)).toNat
  let finish ← IO.monoNanosNow
  return (finish - begin, checksum)

def benchmark : IO Unit := do
  for n in [256, 4096, 16384] do
    let xs := variants n
    let b := List.replicate n (0x55 : UInt8) |>.toByteArray
    let c := List.replicate n (0xa9 : UInt8) |>.toByteArray
    unless AppendProbeStock.tripleAppend xs[0]! b c ==
      AppendProbeOptimized.tripleAppend xs[0]! b c do
      throw <| IO.userError "automatic fusion changed output"
    let iters := if n == 16384 then 1500 else 6000
    for rep in [:5] do
      let mut stockNs : Nat := 0
      let mut fusedNs : Nat := 0
      let mut stockCheck : Nat := 0
      let mut fusedCheck : Nat := 0
      if rep % 2 == 0 then
        let (t0, c0) ← timed AppendProbeStock.tripleAppend xs b c iters
        stockNs := t0
        stockCheck := c0
        let (t1, c1) ← timed AppendProbeOptimized.tripleAppend xs b c iters
        fusedNs := t1
        fusedCheck := c1
      else
        let (t1, c1) ← timed AppendProbeOptimized.tripleAppend xs b c iters
        fusedNs := t1
        fusedCheck := c1
        let (t0, c0) ← timed AppendProbeStock.tripleAppend xs b c iters
        stockNs := t0
        stockCheck := c0
      unless stockCheck == fusedCheck do
        throw <| IO.userError "automatic fusion benchmark checksum mismatch"
      let ratio := fusedNs.toFloat / stockNs.toFloat
      IO.println s!"automatic-append-fusion n={n} iters={iters} rep={rep} stockNs={stockNs} fusedNs={fusedNs} ratio={ratio} checksum={stockCheck}"

end Lean4LeanCompiler.AppendProbeBenchmark

def main : IO Unit := Lean4LeanCompiler.AppendProbeBenchmark.benchmark
