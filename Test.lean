import Zlib

/-- Check that two byte arrays are equal. -/
def ByteArray.beq (a b : ByteArray) : Bool :=
  a.data == b.data

def main : IO Unit := do
  let original := "Hello, world! This is a test of zlib compression from Lean 4. ".toUTF8
  -- Repeat to make compression worthwhile
  let mut big := ByteArray.empty
  for _ in List.range 100 do
    big := big ++ original

  IO.println s!"Original size: {big.size}"

  -- Test zlib compress/decompress
  let compressed ← Zlib.compress big
  IO.println s!"Zlib compressed size: {compressed.size}"
  let decompressed ← Zlib.decompress compressed
  IO.println s!"Zlib decompressed size: {decompressed.size}"
  assert! decompressed.beq big
  IO.println "Zlib roundtrip: OK"

  -- Test gzip compress/decompress
  let gzipped ← Gzip.compress big
  IO.println s!"Gzip compressed size: {gzipped.size}"
  let gunzipped ← Gzip.decompress gzipped
  IO.println s!"Gzip decompressed size: {gunzipped.size}"
  assert! gunzipped.beq big
  IO.println "Gzip roundtrip: OK"

  -- Test compression levels
  let fast ← Gzip.compress big (level := 1)
  let best ← Gzip.compress big (level := 9)
  IO.println s!"Gzip level 1: {fast.size}, level 9: {best.size}"
  assert! best.size ≤ fast.size

  -- Test empty input
  let empty := ByteArray.empty
  let ce ← Zlib.compress empty
  let de ← Zlib.decompress ce
  assert! de.beq empty
  let ge ← Gzip.compress empty
  let gde ← Gzip.decompress ge
  assert! gde.beq empty
  IO.println "Empty input roundtrip: OK"

  IO.println "All tests passed!"
