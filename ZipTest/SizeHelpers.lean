import ZipTest.Helpers

/-! Conformance tests for the size-then-emit dispatch (`deflateRaw`/`deflateCompressed`).

The level-≥5 dispatch sizes the stored/fixed/dynamic candidates from a single
token pass and emits only the winner, replacing the old "emit all three, keep the
smallest" `pickSmaller` cascade. That refactor is byte-identical *iff* the
`fixedBlockBytes`/`dynBlockBytes` cost models equal the emitted block sizes — a
fact the roundtrip proofs do not establish (they hold for whichever block is
chosen). These tests pin that invariant:

1. `fixedBlockBytes`/`dynBlockBytes` equal the actual emitted `.size`.
2. The new `deflateRaw` is byte-identical to the old pickSmaller-of-emitted-blocks
   reference across diverse inputs.
-/

open Zip.Native.Deflate

namespace ZipTest.SizeHelpers

/-- Old level-≥5 behaviour: emit stored, fixed, and dynamic, keep the smallest. -/
private def deflateRawReference (data : ByteArray) : ByteArray :=
  let tokens := lz77LazyIter data
  pickSmaller (Zip.Spec.DeflateStoredCorrect.deflateStoredPure data)
    (pickSmaller (deflateFixedBlock data tokens) (deflateDynamicBlock data tokens))

/-- A small deterministic LCG byte generator for assorted test inputs. -/
private def lcgBytes (seed n : Nat) : ByteArray := Id.run do
  let mut s := seed
  let mut acc := ByteArray.empty
  for _ in [0:n] do
    s := (s * 1103515245 + 12345) % 2147483648
    acc := acc.push (UInt8.ofNat (s / 65536 % 256))
  return acc

/-- `i`-byte block of byte value `b`. -/
private def repeatByte (b n : Nat) : ByteArray :=
  ByteArray.mk (Array.replicate n (UInt8.ofNat b))

private def asciiText (n : Nat) : ByteArray := Id.run do
  let pat := "the quick brown fox jumps over the lazy dog. ".toUTF8
  let mut acc := ByteArray.empty
  let mut i := 0
  while acc.size < n do
    acc := acc.push (pat.get! (i % pat.size))
    i := i + 1
  return acc

/-- All the inputs we check: edge cases, compressible, and incompressible. -/
private def samples : List (String × ByteArray) :=
  [ ("empty", ByteArray.empty),
    ("single", ByteArray.mk #[42]),
    ("two", ByteArray.mk #[0, 255]),
    ("zeros-1k", repeatByte 0 1024),
    ("ones-300", repeatByte 1 300),
    ("text-2k", asciiText 2048),
    ("text-tiny", asciiText 7),
    ("prng-2k", lcgBytes 1 2048),
    ("prng-37", lcgBytes 99 37),
    ("prng-1", lcgBytes 7 1) ]

def tests : IO Unit := do
  IO.println "  SizeHelpers (size-then-emit conformance) tests..."
  for (name, data) in samples do
    let tokens := lz77LazyIter data
    let (lf, df) := tokenFreqs tokens
    -- 1a. fixed cost model == emitted fixed block size
    let fixedSize := fixedBlockBytes lf df
    let fixedEmit := (deflateFixedBlock data tokens).size
    unless fixedSize == fixedEmit do
      throw (IO.userError
        s!"fixedBlockBytes mismatch on {name}: model={fixedSize} emit={fixedEmit}")
    -- 1b. dynamic cost model == emitted dynamic block size
    let (litLens, distLens) := dynamicCodeLengths lf df
    let dynSize := dynBlockBytes lf df litLens distLens
    let dynEmit := (deflateDynamicBlock data tokens).size
    unless dynSize == dynEmit do
      throw (IO.userError
        s!"dynBlockBytes mismatch on {name}: model={dynSize} emit={dynEmit}")
    -- 2. new deflateRaw byte-identical to the old emit-all reference (level 6)
    let newOut := deflateRaw data 6
    let refOut := deflateRawReference data
    unless newOut.beq refOut do
      throw (IO.userError
        s!"deflateRaw(6) not byte-identical to reference on {name}: \
           new.size={newOut.size} ref.size={refOut.size}")
    -- the chosen output must still inflate back to the input
    match Zip.Native.Inflate.inflate newOut (data.size + 64) with
    | .ok back =>
      unless back.beq data do
        throw (IO.userError s!"deflateRaw(6) roundtrip mismatch on {name}")
    | .error e => throw (IO.userError s!"deflateRaw(6) inflate failed on {name}: {e}")
  IO.println "  SizeHelpers tests passed."

end ZipTest.SizeHelpers
