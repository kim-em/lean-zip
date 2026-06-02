import ZipTest.Helpers

/-! Smoke tests for the Track D zopfli comparator.

When the project is built without zopfli the FFI raises an `IO.userError`
containing `"zopfli: not built with"`; we treat that as a clean skip. zopfli is
compress-only (its output is ordinary raw DEFLATE), so the roundtrip is checked
by decoding with the native (verified) inflate and the zlib FFI. zopfli is slow,
so the inputs here are deliberately small. -/

namespace ZipTest.Zopfli

private def disabledMarker : String := "zopfli: not built with"

private def withZopfli (description : String) (action : IO α) (k : α → IO Unit) : IO Unit := do
  match (← action.toBaseIO) with
  | .ok x => k x
  | .error e =>
    if (toString e).contains disabledMarker then
      IO.println s!"Zopfli tests skipped ({description}): comparator disabled"
    else
      throw e

private def roundtrips (label : String) (data : ByteArray) : IO Unit := do
  let z ← Zopfli.compress data
  match Zip.Native.Inflate.inflate z with
  | .ok back => assert! back.beq data
  | .error e => throw (IO.userError s!"native inflate rejected zopfli output ({label}): {e}")
  assert! (← RawDeflate.decompress z).beq data

def tests : IO Unit := do
  withZopfli "compress(prng)" (Zopfli.compress (mkPrngData 1024)) fun _ => do
    -- A few small payloads, decoded by the verified inflate and zlib.
    roundtrips "prng" (mkPrngData 1024)
    roundtrips "constant" (mkConstantData 2048)
    roundtrips "cyclic" (mkCyclicData 2048)
    roundtrips "empty" ByteArray.empty

    -- More iterations must still produce a valid (and no larger) stream.
    let constant := mkConstantData 4096
    let z15 ← Zopfli.compress constant
    let z50 ← Zopfli.compress constant (iterations := 50)
    match Zip.Native.Inflate.inflate z50 with
    | .ok back => assert! back.beq constant
    | .error e => throw (IO.userError s!"native inflate rejected zopfli(iter=50): {e}")
    assert! z50.size ≤ z15.size

    IO.println "Zopfli tests: OK"

end ZipTest.Zopfli
