import Zip
import ZipTest.Helpers

/-! Differential conformance for the table-driven Huffman decoder.

`Zip.Native.HuffTree.decodeWithTable` (the fast-bits lookup table introduced for
faster inflate) must decode every bitstream identically to the canonical
`HuffTree.decode` tree walk — same symbol, same consumed bit position, same
error behaviour. `HuffTree.decode` carries no `@[implemented_by]` override, so
this is a genuine head-to-head check of the two decoders (the end-to-end
roundtrip/fuzz suites only ever exercise the fast path, which `decodeHuffman`'s
`@[implemented_by]` routes them through).

Trees are chosen to cover every code-length regime:
- codes shorter than `fastBits` (direct table hit),
- codes exactly `fastBits` long (table hit at the boundary),
- codes longer than `fastBits` (tree-walk fallback),
- a single mixed tree with code lengths 1…15 (both paths in one table),
- the RFC 1951 fixed literal/length and distance trees.

Bitstreams include byte-aligned and bit-offset starts, and deliberately short
inputs so the `bitsAvail` "not enough bits left" fallback fires. -/

namespace ZipTest.InflateTable

open Zip.Native (HuffTree)
open ZipCommon (BitReader)

/-- 64-bit xorshift PRNG (same shape as the inflate fuzz driver). -/
private def xorshift64 (s : UInt64) : UInt64 := Id.run do
  let mut x := s
  x := x ^^^ (x <<< 13)
  x := x ^^^ (x >>> 7)
  x := x ^^^ (x <<< 17)
  return x

/-- A complete Huffman tree: `2^depth` symbols, every code length `depth`.
    `depth = fastBits` sits exactly on the table boundary; `depth > fastBits`
    forces the tree-walk fallback for every symbol. -/
private def completeLengths (depth : Nat) : Array UInt8 :=
  Array.replicate (2 ^ depth) depth.toUInt8

/-- Canonical "spine" code lengths 1,2,…,14,15,15 — a valid prefix code (Kraft
    sum = 1) mixing fast (≤ `fastBits`) and fallback (> `fastBits`) codes in a
    single tree. -/
private def spineLengths : Array UInt8 :=
  (Array.range 14 |>.map (fun i => (i + 1).toUInt8)) ++ #[15, 15]

/-- The trees exercised by the differential check, paired with a label. -/
private def trees : Array (String × HuffTree) := Id.run do
  let mut acc : Array (String × HuffTree) := #[]
  for d in [1, 4, 8, 9, 10, 12] do
    match HuffTree.fromLengths (completeLengths d) 15 with
    | .ok t => acc := acc.push (s!"complete-{d}", t)
    | .error _ => pure ()
  match HuffTree.fromLengths spineLengths 15 with
  | .ok t => acc := acc.push ("spine-1..15", t)
  | .error _ => pure ()
  match HuffTree.fromLengths Zip.Native.Inflate.fixedLitLengths with
  | .ok t => acc := acc.push ("fixed-lit", t)
  | .error _ => pure ()
  match HuffTree.fromLengths Zip.Native.Inflate.fixedDistLengths with
  | .ok t => acc := acc.push ("fixed-dist", t)
  | .error _ => pure ()
  return acc

/-- Compare two decode results for behavioural equality: same `ok`/`error`
    disposition, and on success the same symbol and the same consumed position
    (`pos`, `bitOff`). The error *string* is not compared — only that both
    decoders agree on success vs. failure. -/
private def sameResult (a b : Except String (UInt16 × BitReader)) : Bool :=
  match a, b with
  | .ok (s₁, r₁), .ok (s₂, r₂) => s₁ == s₂ && r₁.pos == r₂.pos && r₁.bitOff == r₂.bitOff
  | .error _, .error _ => true
  | _, _ => false

/-- Run the table decoder and the tree-walk decoder over `tree` from every bit
    offset of `data`, returning a mismatch description on the first divergence. -/
private def checkStream (label : String) (tree : HuffTree) (table : Array (UInt16 × UInt8))
    (data : ByteArray) : Option String := Id.run do
  for startPos in [:data.size] do
    for bitOff in [:8] do
      let br : BitReader := { data, pos := startPos, bitOff }
      let fast := tree.decodeWithTable table br
      let slow := tree.decode br
      unless sameResult fast slow do
        return some s!"[{label}] mismatch at pos={startPos} bitOff={bitOff}"
  return none

/-- Drive every tree over a batch of PRNG-generated bitstreams (varied lengths,
    including very short inputs that trip the not-enough-bits fallback). Throws
    on the first mismatch. -/
def tests : IO Unit := do
  IO.println "  InflateTable differential tests (table decode vs tree walk)..."
  let mut s : UInt64 := 0x7a61_626c_6544_3035
  let sizes := #[1, 2, 3, 5, 8, 13, 33, 64]
  let mut checks : Nat := 0
  for (label, tree) in trees do
    let table := tree.buildTable
    for sz in sizes do
      -- Generate `sz` pseudo-random bytes.
      let mut bytes := ByteArray.empty
      for _ in [:sz] do
        s := xorshift64 s
        bytes := bytes.push (s &&& 0xFF).toUInt8
      match checkStream label tree table bytes with
      | some msg => throw (IO.userError msg)
      | none => checks := checks + 1
  IO.println s!"    {checks} (tree × stream) batches matched; tables={trees.size}"

end ZipTest.InflateTable
