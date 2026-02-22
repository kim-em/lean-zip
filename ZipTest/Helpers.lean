import Zip

set_option maxRecDepth 2048

/-- Check that two byte arrays are equal. -/
def ByteArray.beq (a b : ByteArray) : Bool :=
  a.data == b.data

/-- Read a test fixture from testdata/ directory. -/
def readFixture (path : String) : IO ByteArray :=
  IO.FS.readBinFile s!"testdata/{path}"

/-- Write fixture data to a temp file, returning the path. -/
def writeFixtureTmp (name : String) (data : ByteArray) : IO System.FilePath := do
  let path : System.FilePath := s!"/tmp/lean-zip-fixture-{name}"
  IO.FS.writeBinFile path data
  return path

/-- Assert that an IO action throws an error containing the given substring. -/
def assertThrows (description : String) (action : IO Unit) (errorSubstring : String) : IO Unit := do
  let sentinel := "<<ASSERT_THROWS_FAIL>>"
  try
    action
    throw (IO.userError s!"{sentinel}{description}: expected error containing '{errorSubstring}' but succeeded")
  catch e =>
    let msg := toString e
    if msg.contains sentinel then
      throw e
    else if msg.contains errorSubstring then
      pure ()
    else
      throw (IO.userError s!"{sentinel}{description}: expected '{errorSubstring}' but got: {msg}")

/-- Create a readable IO.FS.Stream backed by a ByteArray.
    Each `read n` returns up to `n` bytes from the current position. -/
def byteArrayReadStream (data : ByteArray) : IO IO.FS.Stream := do
  let posRef ← IO.mkRef 0
  return {
    flush := pure ()
    read := fun n => do
      let pos ← posRef.get
      let available := data.size - pos
      let toRead := min n.toNat available
      let result := data.extract pos (pos + toRead)
      posRef.set (pos + toRead)
      return result
    write := fun _ => throw (IO.userError "byteArrayReadStream: write not supported")
    getLine := pure ""
    putStr := fun _ => pure ()
    isTty := pure false
  }

/-- Wrap an IO.FS.Stream so that each `read` returns at most `maxChunk` bytes.
    Simulates short reads from pipes or network streams. -/
def fragmentingStream (inner : IO.FS.Stream) (maxChunk : Nat) : IO.FS.Stream := {
  flush := inner.flush
  read := fun n => inner.read (min n maxChunk.toUSize)
  write := inner.write
  getLine := inner.getLine
  putStr := inner.putStr
  isTty := inner.isTty
}

/-- Create the standard test data (100x repeated string, 6200 bytes). -/
def mkTestData : IO ByteArray := do
  let original := "Hello, world! This is a test of zlib compression from Lean 4. ".toUTF8
  let mut big := ByteArray.empty
  for _ in [:100] do
    big := big ++ original
  return big

/-- Create large test data (2000x repeated string, 124000 bytes). -/
def mkLargeData : IO ByteArray := do
  let original := "Hello, world! This is a test of zlib compression from Lean 4. ".toUTF8
  let mut large := ByteArray.empty
  for _ in [:2000] do
    large := large ++ original
  return large

/-- Create pseudo-random (incompressible) test data of `n` bytes. -/
def mkRandomData (n : Nat := 1000) : ByteArray := Id.run do
  let mut result := ByteArray.empty
  for i in [:n] do
    result := result.push ((i * 73 + 137) % 256).toUInt8
  return result

/-- All bytes are 0x42. Maximally compressible. -/
def mkConstantData (size : Nat) : ByteArray := Id.run do
  let mut result := ByteArray.empty
  for _ in [:size] do
    result := result.push 0x42
  return result

/-- Cycle through 16 distinct bytes. Highly compressible but exercises Huffman coding. -/
def mkCyclicData (size : Nat) : ByteArray := Id.run do
  let pattern : Array UInt8 := #[0x00, 0x11, 0x22, 0x33, 0x44, 0x55, 0x66, 0x77,
                                   0x88, 0x99, 0xAA, 0xBB, 0xCC, 0xDD, 0xEE, 0xFF]
  let mut result := ByteArray.empty
  for i in [:size] do
    result := result.push pattern[i % 16]!
  return result

/-- Deterministic pseudo-random bytes via xorshift32. Much less compressible than cyclic. -/
def mkPrngData (size : Nat) (seed : UInt32 := 2463534242) : ByteArray := Id.run do
  let mut state := seed
  let mut result := ByteArray.empty
  for _ in [:size] do
    state := state ^^^ (state <<< 13)
    state := state ^^^ (state >>> 17)
    state := state ^^^ (state <<< 5)
    result := result.push (state &&& 0xFF).toUInt8
  return result

/-- Time an IO action, returning (result, elapsed_ms). -/
def timeIO (action : IO α) : IO (α × Float) := do
  let start ← IO.monoNanosNow
  let result ← action
  let stop ← IO.monoNanosNow
  let elapsedMs := (stop - start).toFloat / 1_000_000.0
  return (result, elapsedMs)

/-- Human-readable size name: 1024 → "1KB", 1048576 → "1MB". -/
def sizeName (n : Nat) : String :=
  if n ≥ 1048576 then s!"{n / 1048576}MB"
  else if n ≥ 1024 then s!"{n / 1024}KB"
  else s!"{n}B"
