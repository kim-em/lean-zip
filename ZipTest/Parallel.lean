import ZipTest.Helpers

/-! Runtime checks for the opt-in chunk-parallel encoder (`Zip.Native.Parallel`).

`deflateDynamicBlocksSCParallel_eq` proves the threading flag cannot change the
bytes, and the four `deflateDynamicBlocksSC` theorems are restated for
it.  What the proofs do *not* cover is the code generator: that the compiled
`Task.spawn` path really computes what the model says.  These tests pin that.

Chunk sizes here are deliberately tiny so the samples actually split.

Throughput is measured in `conformance/Conformance/ParallelBench.lean`, alongside
the other benchmarks. -/

open Zip.Native
open Zip.Native.Deflate

namespace ZipTest.Parallel

private def samples : List (String × ByteArray) :=
  [ ("text", mkTextData 200000)
  , ("cyclic", mkCyclicData 150000)
  , ("prng", mkPrngData 120000)
  , ("constant", mkConstantData 90000)
  , ("tiny", mkTextData 17)
  ]

private def checkOne (name : String) (data : ByteArray) (level : UInt8) (cs : Nat) : IO Unit := do
  let seq := deflateDynamicBlocksSCParallel data cs level false
  let par := deflateDynamicBlocksSCParallel data cs level true
  unless seq == par do
    throw (IO.userError s!"par/seq mismatch on {name} L{level} cs={cs}: \
{seq.size} vs {par.size} bytes")
  match Inflate.inflate par (maxOutputSize := 64 * 1024 * 1024) with
  | .error e => throw (IO.userError s!"inflate failed on {name} L{level} cs={cs}: {e}")
  | .ok back =>
    unless back == data do
      throw (IO.userError s!"roundtrip mismatch on {name} L{level} cs={cs}: \
{back.size} vs {data.size} bytes")

def tests : IO Unit := do
  IO.println "  Chunk-parallel deflate tests..."
  for (name, data) in samples do
    for level in List.range 11 do
      for cs in [4096, 65536, 1 <<< 20] do
        checkOne name data level.toUInt8 cs
  -- Threaded output must equal the unthreaded encoder byte for byte.
  for (name, data) in samples do
    for cs in [4096, 65536] do
      unless deflateDynamicBlocksSCParallel data cs 6 true == deflateDynamicBlocksSC data cs 6 do
        throw (IO.userError s!"threaded output differs from deflateDynamicBlocksSC on {name}")
  IO.println "  Chunk-parallel deflate tests passed."

end ZipTest.Parallel
