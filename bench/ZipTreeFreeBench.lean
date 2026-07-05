import Zip.Native.Inflate

/-!
# Build-cost micro-benchmark: tree+table vs tree-free canonical table

The tree-free decode win comes from the per-block *build* phase: the current
path builds a Huffman tree (`fromLengths`) **and** the fast table (`buildTable`),
whereas a tree-free path builds only the canonical table
(`buildTableCanonicalFast`) plus a cheap long-code structure. The symbol-decode
loop is identical for the common ≤9-bit codes, and long codes are rare, so the
build delta is the dominant term of the win.

This standalone benchmark times the build procedures in isolation (many
iterations over realistic DEFLATE code-length vectors) to decide whether the
tree-free path is worth the full implementation + proof, *before* paying for it.
-/

open Zip.Native
open Zip.Native.HuffTree

/-- Time `act` `iters` times; return ns/op. `act` returns a live nonzero value. -/
def timePerOp (iters : Nat) (act : IO Nat) : IO Nat := do
  let t0 ← IO.monoNanosNow
  let mut acc : Nat := 0
  for _ in [:iters] do
    acc := acc + (← act)
  let t1 ← IO.monoNanosNow
  if acc == 0 then IO.eprintln "unreachable"
  return (t1 - t0) / (max iters 1)

/-- A complete `d`-bit code: `2^d` symbols all of length `d`. -/
def completeLengths (d : Nat) : Array UInt8 := Array.replicate (2 ^ d) d.toUInt8

/-- A 1..15 "spine": one symbol of each length 1..15 plus a filler length-15. -/
def spineLengths : Array UInt8 :=
  (Array.range 15).map (fun i => (i + 1).toUInt8) ++ #[(15 : UInt8)]

/-- A realistic-shape dynamic lit/len vector: a 286-symbol table with a plausible
    length distribution (many short 5–8-bit codes, a tail up to 14 bits, gaps). -/
def realisticLitLen : Array UInt8 := Id.run do
  let mut a : Array UInt8 := Array.replicate 286 0
  -- common literals at length 8 (Kraft 2^7 each): 144 × 128 = 18432
  for i in [:144] do
    a := a.set! i (8 : UInt8)
  -- length codes 256–279 at length 7 (2^8 each): 24 × 256 = 6144
  for i in [256:280] do
    a := a.set! i (7 : UInt8)
  -- sparse long tail at length 10 (2^5 each): 6 × 32 = 192
  for i in [280:286] do
    a := a.set! i (10 : UInt8)
  -- total Kraft 24768 ≤ 32768: a valid (under-subscribed) code
  return a

/-- The benchmark length vectors (label, lengths). -/
def vectors : Array (String × Array UInt8) :=
  #[ ("fixed-lit (288)", Inflate.fixedLitLengths),
     ("fixed-dist (32)", Inflate.fixedDistLengths),
     ("realistic-litlen (286)", realisticLitLen),
     ("complete-9 (512)", completeLengths 9),
     ("spine-1..15", spineLengths) ]

/-- Build the current path: tree (`fromLengths`) + fast table (`buildTable`). -/
def buildTreePath (lengths : Array UInt8) : Nat :=
  match HuffTree.fromLengths lengths 15 with
  | .ok tree => (tree.buildTable.packed[0]!).toNat + 1
  | .error _ => 0

/-- Build the tree-free path: only the fast canonical table. -/
def buildTreeFree (lengths : Array UInt8) : Nat :=
  (HuffTree.buildTableCanonicalFast lengths 15).packed[0]!.toNat + 1

/-- Build the tree alone (to isolate the tree-build cost). -/
def buildTreeOnly (lengths : Array UInt8) : Nat :=
  match HuffTree.fromLengths lengths 15 with
  | .ok tree => match tree with
    | .node _ _ => 1
    | _ => 1
  | .error _ => 0

def main : IO Unit := do
  let iters := 20000
  IO.println s!"Build-cost micro-benchmark ({iters} iters/op), ns/op:"
  IO.println "  vector | tree+table | tree-free | tree-only | speedup(t+t / t-free)"
  for (label, v) in vectors do
    let tTreeTable ← timePerOp iters (IO.lazyPure (fun _ => buildTreePath v))
    let tTreeFree  ← timePerOp iters (IO.lazyPure (fun _ => buildTreeFree v))
    let tTreeOnly  ← timePerOp iters (IO.lazyPure (fun _ => buildTreeOnly v))
    let speedupX100 := if tTreeFree == 0 then 0 else (tTreeTable * 100) / tTreeFree
    let frac := speedupX100 % 100
    let fracStr := if frac < 10 then s!"0{frac}" else toString frac
    IO.println s!"  {label} | {tTreeTable} | {tTreeFree} | {tTreeOnly} | {speedupX100 / 100}.{fracStr}x"
