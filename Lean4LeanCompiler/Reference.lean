/-
Stock Lean reference declarations. No experimental compiler pass is imported
here. All bytes and arrays use Lean's ordinary runtime representations.
-/
import Lean

namespace Lean4LeanCompiler.Reference

def copyFour (src : ByteArray) : ByteArray := Id.run do
  if src.size < 4 then return ByteArray.empty
  let mut dst := ByteArray.emptyWithCapacity 4
  dst := dst.push (src.get! 0)
  dst := dst.push (src.get! 1)
  dst := dst.push (src.get! 2)
  dst := dst.push (src.get! 3)
  return dst

def reverseFour (src : ByteArray) : ByteArray := Id.run do
  if src.size != 4 then return src
  let a := src.get! 0
  let b := src.get! 1
  let c := src.get! 2
  let d := src.get! 3
  let mut dst := src
  dst := dst.set! 0 d
  dst := dst.set! 1 c
  dst := dst.set! 2 b
  dst := dst.set! 3 a
  return dst

def writeFourInto (src dst : ByteArray) : Option ByteArray := Id.run do
  if src.size < 4 then return none
  if dst.size != 4 then return none
  let a := src.get! 0
  let b := src.get! 1
  let c := src.get! 2
  let d := src.get! 3
  let mut out := dst
  out := out.set! 0 a
  out := out.set! 1 b
  out := out.set! 2 c
  out := out.set! 3 d
  return some out

def bumpList (xs : List UInt8) : List UInt8 :=
  xs.map (· + 1)

end Lean4LeanCompiler.Reference
