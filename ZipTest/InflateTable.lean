import Zip
import ZipTest.Helpers

/-! Differential conformance for the table-driven Huffman decoder.

`Zip.Native.HuffTree.decodeWithTable` (the fast-bits lookup table) decodes every
bitstream identically to the canonical `HuffTree.decode` tree walk — same symbol,
same consumed bit position, same error behaviour. This equality is *proven*
(`Zip.Spec.InflateTable.decodeWithTable_eq`) and the block loop runs the fast
path on the verified route (no `@[implemented_by]` trust gap); these differential
tests are a fast empirical sanity check spanning every code-length regime.

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
  for d in [1, 4, 8, 10, 11, 13] do
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
private def checkStream (label : String) (tree : HuffTree) (table : HuffTree.DecodeTable)
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

/-- The code-length vectors exercised by the canonical-build conformance check,
    spanning every regime: short codes only, codes on the `fastBits` boundary,
    codes past it (sentinel slots), a 1…15 mix, and the RFC fixed code lengths. -/
private def lengthVectors : Array (String × Array UInt8) := Id.run do
  let mut acc : Array (String × Array UInt8) := #[]
  for d in [1, 4, 8, 10, 11, 13] do
    acc := acc.push (s!"complete-{d}", completeLengths d)
  acc := acc.push ("spine-1..15", spineLengths)
  acc := acc.push ("fixed-lit", Zip.Native.Inflate.fixedLitLengths)
  acc := acc.push ("fixed-dist", Zip.Native.Inflate.fixedDistLengths)
  -- A sparse, irregular *incomplete* code (Kraft sum < 1, so some ≤ fastBits
  -- slots stay sentinel) mixing short codes with one length-13 fallback code —
  -- the realistic dynamic-block shape.
  acc := acc.push ("sparse", #[3, 3, 2, 0, 4, 4, 0, 0, 2, 13, 13] ++ Array.replicate 5 (0 : UInt8))
  return acc

/-- Differential check: the canonical O(n) table build (`buildTableCanonical`)
    produces the exact same packed table as the tree-built `buildTable`, for
    every code-length regime. This is the runtime witness of the equality
    `buildTableCanonical lengths = buildTable (fromLengthsTree lengths)` whose
    formal proof (`buildTableCanonical_eq`) lands in a follow-up; its supporting
    lemmas are already in `Zip.Spec.InflateCanonical`. -/
def canonicalTests : IO Unit := do
  IO.println "  InflateTable canonical-build tests (canonical fill vs tree build)..."
  let mut checks : Nat := 0
  for (label, lengths) in lengthVectors do
    match HuffTree.fromLengths lengths 15 with
    | .error e => throw (IO.userError s!"[{label}] fromLengths failed: {e}")
    | .ok tree =>
      let treeTable := tree.buildTable
      let canonTable := HuffTree.buildTableCanonical lengths 15
      unless treeTable.packed == canonTable.packed do
        -- Report the first divergent slot for diagnosis.
        let mut bad : Option Nat := none
        for i in [:treeTable.packed.size] do
          if bad.isNone && treeTable.packed[i]! != canonTable.packed[i]! then
            bad := some i
        throw (IO.userError
          s!"[{label}] canonical table differs from tree table at slot {bad}")
      checks := checks + 1
      -- The fast array-based build (no List allocation / WF recursion) must
      -- produce the byte-identical packed table as the spec-function build.
      let fastTable := HuffTree.buildTableCanonicalFast lengths 15
      unless canonTable.packed == fastTable.packed do
        let mut bad : Option Nat := none
        for i in [:canonTable.packed.size] do
          if bad.isNone && canonTable.packed[i]! != fastTable.packed[i]! then
            bad := some i
        throw (IO.userError
          s!"[{label}] fast canonical table differs from spec canonical table at slot {bad}")
  IO.println s!"    {checks} length vectors: canonical (spec + fast) build matches tree build"

/-- Differential check for the libdeflate-style subtable long-code path (#2801):
    the production `decodeSymCanon` (11-bit root table + boxing-free `subLookup`
    subtable fallback for >`fastBits` codes) decodes every buffer identically to the
    canonical tree `decodeSym` — same symbol, consumed bits, and error behaviour.
    This is the runtime witness of `subLookup_ok_iff_walkCanonical` /
    `decodeSymCanon_ok_iff_decodeSym`; it exercises the 12-15-bit subtable slots the
    root table misses, across every code-length regime including the near-EOF
    "not enough bits" fallback (small `cnt`). -/
def subtableTests : IO Unit := do
  IO.println "  InflateTable subtable tests (subLookup fallback vs tree decodeSym)..."
  let mut s : UInt64 := 0x5375_6254_6162_6c65
  let cnts := #[0, 1, 5, 11, 12, 13, 14, 15, 20, 40, 56]
  let mut checks : Nat := 0
  for (label, lengths) in lengthVectors do
    match HuffTree.fromLengths lengths 15 with
    | .error _ => pure ()  -- skip invalid length sets
    | .ok tree =>
      -- the production build: root fast table augmented in place with inline
      -- subtable offsets, plus the flat `subs`
      let tf := HuffTree.buildTreeFreeWithCount lengths (HuffTree.countLengthsFast lengths 15) 15
      for _ in [:4000] do
        s := xorshift64 s
        let buf := s
        for cnt in cnts do
          let a := (HuffTree.decodeSymCanon tf.2 tf.1 15 buf cnt).toOption
          let b := (Zip.Native.InflateBuf.decodeSym tree tf.1 buf cnt).toOption
          unless a == b do
            throw (IO.userError
              s!"[{label}] decodeSymCanon (subtable) ≠ tree decodeSym at buf={buf} cnt={cnt}")
          checks := checks + 1
  IO.println s!"    {checks} (length-vector × buffer × cnt) subtable decodes matched tree walk"

end ZipTest.InflateTable
