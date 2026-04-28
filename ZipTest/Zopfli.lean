import ZipTest.Helpers

/-! Smoke tests for the zopfli FFI binding.

Zopfli is the maximum-compression DEFLATE encoder used as the Track D
ratio quality ceiling. It is encode-only and intentionally ~100× slower
than zlib level 9, so we keep tests small (≤ 4 KB). -/

def ZipTest.Zopfli.tests : IO Unit := do
  -- 1. Roundtrip via the native (pure-Lean) inflate decoder, on a 4 KB
  --    text input. This exercises the deflate framing zopfli emits.
  let txt := mkTextData 4096
  -- Use 5 iterations to keep the test fast; default 15 is for production runs.
  let zopfliOut ← Zopfli.compress txt (iterations := 5)
  match Zip.Native.Inflate.inflate zopfliOut with
  | .ok decoded =>
    unless decoded.beq txt do
      throw (IO.userError "zopfli roundtrip: native inflate produced different bytes")
  | .error e =>
    throw (IO.userError s!"zopfli roundtrip: native inflate failed: {e}")

  -- 2. Quality sanity check: zopfli output must be ≤ zlib level-9 output on
  --    text. A fallback to plain zlib (or raw bytes) would fail this.
  let zlib9 ← RawDeflate.compress txt (level := 9)
  unless zopfliOut.size ≤ zlib9.size do
    throw (IO.userError s!"zopfli quality regression: zopfli={zopfliOut.size} bytes \
      > zlib level 9={zlib9.size} bytes (likely linked the wrong library)")

  -- 3. Empty input still produces a decodable raw deflate stream.
  let empty ← Zopfli.compress ByteArray.empty (iterations := 1)
  unless empty.size > 0 do
    throw (IO.userError "zopfli on empty input produced zero bytes")
  match Zip.Native.Inflate.inflate empty with
  | .ok decoded =>
    unless decoded.beq ByteArray.empty do
      throw (IO.userError "zopfli empty roundtrip: native inflate decoded non-empty bytes")
  | .error e =>
    throw (IO.userError s!"zopfli empty roundtrip: native inflate failed: {e}")

  -- 4. iterations = 0 is rejected at the FFI boundary.
  match ← (Zopfli.compress txt (iterations := 0)).toBaseIO with
  | .ok _ => throw (IO.userError "zopfli iterations=0 should have been rejected")
  | .error e =>
    unless (toString e).contains "numIterations" do
      throw (IO.userError s!"zopfli iterations=0 wrong error: {e}")

  IO.println "Zopfli tests: OK"
