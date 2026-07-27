import Zip.Native.DeflateFreqsFused

/-! Focused compiled-path checks for the level-one packed `UInt32` head table.
    The proof in `Zip.Spec.DeflatePackedHeadCorrect` covers every input; these
    tests pin the representation boundary cases and the FFI's copy-on-write
    behavior. -/

namespace ZipTest.PackedHeads

open Zip.Native.Deflate

private def emptyHeads : ByteArray :=
  ByteArray.mk (Array.replicate (65536 * 4) 0)

private theorem emptyHeads_size : emptyHeads.size = 65536 * 4 := by
  change (Array.replicate (65536 * 4) (0 : UInt8)).size = 65536 * 4
  rw [Array.size_replicate]

/-- Pure Lean model of the four-byte little-endian extern store. -/
private def refUset32LE (a : ByteArray) (off : Nat) (v : UInt32) : ByteArray :=
  (((a.set! off v.toUInt8).set!
    (off + 1) (v >>> 8).toUInt8).set!
    (off + 2) (v >>> 16).toUInt8).set!
    (off + 3) (v >>> 24).toUInt8

/-- Compare the extern with its pure model at aligned and unaligned offsets,
    including distinct bytes, zeros, and all ones. Keeping the source and an
    independent snapshot live also checks the shared-buffer copy path. -/
private def writerConformanceTest : IO Unit := do
  let source := ByteArray.mk (Array.range 12 |>.map (fun i => i.toUInt8))
  let snapshot := source.extract 0 source.size
  for off in ([0, 1, 4, 8] : List USize) do
    if h : off.toNat + 4 ≤ source.size then
      for value in ([0x89ABCDEF, 0, 0xFFFFFFFF] : List UInt32) do
        let got := source.usetUInt32LE off value h
        let want := refUset32LE source off.toNat value
        unless got == want do
          throw (IO.userError
            s!"usetUInt32LE mismatch at offset {off.toNat}, value {value}")
        unless source == snapshot do
          throw (IO.userError
            s!"usetUInt32LE modified its shared source at offset {off.toNat}")

private def assertEntriesEqual (label : String) (data : ByteArray) : IO Unit := do
  let packed := lz77ChainIterPMergedDirectHeadFNU64 data
  let arrayRef := lz77ChainIterPMergedDirectHeadArrayFNU64 data
  unless packed.1.bytes == arrayRef.1.bytes do
    throw (IO.userError s!"{label}: packed/Array token mismatch")
  unless packed.2.1 == arrayRef.2.1 do
    throw (IO.userError s!"{label}: packed/Array literal-frequency mismatch")
  unless packed.2.2 == arrayRef.2.2 do
    throw (IO.userError s!"{label}: packed/Array distance-frequency mismatch")

/-- Zero is unseen, so position zero must round-trip through the stored code
    `1`. The repeated `abca` prefix also forces the compiled matcher to consume
    position zero as a live distance-three candidate. -/
private def positionZeroTest : IO Unit := do
  let written := emptyHeads.usetUInt32LE 0 1 (by
    rw [emptyHeads_size]
    decide)
  let code := written.ugetUInt32LE 0 (by
    rw [size_usetUInt32LE, emptyHeads_size]
    decide)
  unless code == 1 && (code - 1).toNat == 0 do
    throw (IO.userError "packed head position zero did not round-trip as code 1")
  let repeated := ByteArray.mk #[97, 98, 99, 97, 98, 99, 97]
  let packed := lz77ChainIterPMergedDirectHeadFNU64 repeated
  let recovered := packed.1.toArray.any fun word =>
    match unpackTok word with
    | .reference len dist => 3 ≤ len && dist == 3
    | .literal _ => false
  unless recovered do
    throw (IO.userError "packed matcher did not recover the position-zero abca head")
  assertEntriesEqual "position-zero-repeat" repeated

/-- Bucket 65535 begins at byte offset `4 * 65535 = 262140`; pin the final
    aligned slot so an off-by-one table allocation cannot hide in corpus tests. -/
private def lastBucketTest : IO Unit := do
  let off : USize := 262140
  have hoff : off.toNat + 4 ≤ emptyHeads.size := by
    have hoffN : off.toNat = 262140 := by
      unfold off
      exact USize.toNat_ofNat_of_lt
        (Nat.lt_of_lt_of_le (by decide) USize.le_size)
    rw [hoffN, emptyHeads_size]
    omega
  let value : UInt32 := 0x89ABCDEF
  let written := emptyHeads.usetUInt32LE off value hoff
  have hread : off.toNat + 4 ≤ written.size := by
    rw [size_usetUInt32LE]
    exact hoff
  unless written.ugetUInt32LE off hread == value do
    throw (IO.userError "packed head bucket 65535 did not round-trip")

/-- `usetUInt32LE` may mutate only an exclusive buffer.  Keeping an alias live
    forces the shared-buffer copy path; the alias must remain all-zero while
    the returned buffer receives the write. -/
private def copyOnWriteTest : IO Unit := do
  let shared := emptyHeads
  let alias := shared
  have hwrite : (0 : USize).toNat + 4 ≤ shared.size := by
    rw [emptyHeads_size]
    decide
  let changed := shared.usetUInt32LE 0 0x12345678 hwrite
  have halias : (0 : USize).toNat + 4 ≤ alias.size := by
    rw [emptyHeads_size]
    decide
  have hchanged : (0 : USize).toNat + 4 ≤ changed.size := by
    rw [size_usetUInt32LE]
    exact hwrite
  unless alias.ugetUInt32LE 0 halias == 0 do
    throw (IO.userError "usetUInt32LE modified a shared ByteArray alias")
  unless changed.ugetUInt32LE 0 hchanged == 0x12345678 do
    throw (IO.userError "usetUInt32LE copy-on-write result lost its store")

/-- Sizes below three take the explicit production fallback.  The enormous
    addressability/`UInt32` guard failures cannot be allocated in a practical
    unit test and are covered universally by the entry equivalence theorem. -/
private def wrapperFallbackTest : IO Unit := do
  assertEntriesEqual "fallback-size0" ByteArray.empty
  assertEntriesEqual "fallback-size1" (ByteArray.mk #[42])
  assertEntriesEqual "fallback-size2" (ByteArray.mk #[42, 42])
  assertEntriesEqual "active-size3" (ByteArray.mk #[7, 7, 7])

def tests : IO Unit := do
  IO.println "  PackedHeads tests..."
  writerConformanceTest
  positionZeroTest
  lastBucketTest
  copyOnWriteTest
  wrapperFallbackTest
  IO.println "  PackedHeads tests passed"

end ZipTest.PackedHeads
