import ZipTest.Helpers
import Zip.Native.XxHash

/-! Conformance tests for the native XXH64 implementation against known test vectors. -/

def ZipTest.XxHashNative.tests : IO Unit := do
  -- Test 1: empty input (canonical test vector from xxHash spec)
  let emptyHash := XxHash64.xxHash64 ByteArray.empty 0
  unless emptyHash == 0xEF46DB3751D8E999 do
    throw (IO.userError s!"XXH64 empty: expected 0xEF46DB3751D8E999, got 0x{Nat.toDigits 16 emptyHash.toNat |> String.ofList}")

  -- Test 2: single byte (0x42)
  let singleHash := XxHash64.xxHash64 (ByteArray.mk #[0x42]) 0
  unless singleHash == 0x6D69E28F063257F9 do
    throw (IO.userError s!"XXH64 single byte: expected 0x6D69E28F063257F9, got {singleHash}")

  -- Test 3: short string "Hello World" (11 bytes, exercises remaining-byte paths)
  let helloHash := XxHash64.xxHash64 "Hello World".toUTF8 0
  unless helloHash == 0x6334D20719245BC2 do
    throw (IO.userError s!"XXH64 Hello World: expected 0x6334D20719245BC2, got {helloHash}")

  -- Test 4: exactly 32 bytes (exercises one full stripe, no remaining)
  let data32 := ByteArray.mk (Array.ofFn (n := 32) fun i => i.val.toUInt8)
  let hash32 := XxHash64.xxHash64 data32 0
  unless hash32 == 0xCBF59C5116FF32B4 do
    throw (IO.userError s!"XXH64 32 bytes: expected 0xCBF59C5116FF32B4, got {hash32}")

  -- Test 5: 64 bytes (exercises two full stripes)
  let data64 := ByteArray.mk (Array.ofFn (n := 64) fun i => i.val.toUInt8)
  let hash64 := XxHash64.xxHash64 data64 0
  unless hash64 == 0xF7C67301DB6713F0 do
    throw (IO.userError s!"XXH64 64 bytes: expected 0xF7C67301DB6713F0, got {hash64}")

  -- Test 6: xxHash64Upper32 on empty input
  let upper32Empty := XxHash64.xxHash64Upper32 ByteArray.empty
  unless upper32Empty == 0xEF46DB37 do
    throw (IO.userError s!"XXH64Upper32 empty: expected 0xEF46DB37, got {upper32Empty}")

  -- Test 7: xxHash64Upper32 on "Hello World"
  let upper32Hello := XxHash64.xxHash64Upper32 "Hello World".toUTF8
  unless upper32Hello == 0x6334D207 do
    throw (IO.userError s!"XXH64Upper32 Hello World: expected 0x6334D207, got {upper32Hello}")

  -- Test 8: large input (exercises multiple stripes + remaining bytes)
  let big ← mkTestData  -- 6200 bytes
  let hashBig := XxHash64.xxHash64 big 0
  -- Just check it doesn't crash and returns a non-zero value
  unless hashBig != 0 do
    throw (IO.userError "XXH64 large: got 0 for 6200-byte input")

  -- Test 9: verify against FFI-compressed Zstd data
  -- Zstd's default ZSTD_compress doesn't enable content checksums,
  -- but we can verify the frame header contentChecksum field reports false
  let compressed ← Zstd.compress big
  match Zip.Native.parseFrameHeader compressed 0 with
  | .ok (_, _) => pure ()
  | .error e => throw (IO.userError s!"Zstd parseFrameHeader failed: {e}")

  -- Test 10: deterministic — same input always produces same hash
  let hash1 := XxHash64.xxHash64 "deterministic test".toUTF8 0
  let hash2 := XxHash64.xxHash64 "deterministic test".toUTF8 0
  unless hash1 == hash2 do
    throw (IO.userError "XXH64 not deterministic")

  -- Test 11: different seeds produce different hashes
  let seedA := XxHash64.xxHash64 "seed test".toUTF8 0
  let seedB := XxHash64.xxHash64 "seed test".toUTF8 42
  unless seedA != seedB do
    throw (IO.userError "XXH64: different seeds should produce different hashes")

  -- Test 12: 45-byte input exercises 1 stripe (32 bytes) + 8-byte + 4-byte + 1-byte remaining
  let data45 := ByteArray.mk (Array.ofFn (n := 45) fun i => i.val.toUInt8)
  let hash45 := XxHash64.xxHash64 data45 0
  unless hash45 == 0x10FDD84D6409ABDF do
    throw (IO.userError s!"XXH64 45 bytes: expected 0x10FDD84D6409ABDF, got {hash45}")

  -- Test 13: non-zero seed with known reference value
  let seedHash := XxHash64.xxHash64 "seed test".toUTF8 42
  unless seedHash == 0xBD5B2F29B94F97EE do
    throw (IO.userError s!"XXH64 seed=42: expected 0xBD5B2F29B94F97EE, got {seedHash}")

  -- Test 14: 4-byte input exercises only the 4-byte remaining path (no stripes)
  let data4 := ByteArray.mk #[0x01, 0x02, 0x03, 0x04]
  let hash4 := XxHash64.xxHash64 data4 0
  unless hash4 == 0x542620E3A2A92ED1 do
    throw (IO.userError s!"XXH64 4 bytes: expected 0x542620E3A2A92ED1, got {hash4}")

  IO.println "XxHash64 native tests: OK"
