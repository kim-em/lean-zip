import ZipTest.Helpers

/-! Smoke tests for Track E P5.1 bounded-read helpers: exercises each of
    `Archive.readBoundedSpanFromHandle`, `Archive.readBoundedExactFromHandle`,
    `Tar.readBoundedExactFromStream`, and `Tar.readBoundedEntryData` on a
    happy path and a representative validation-failure path. -/

namespace ZipTest.BoundedRead

/-- Fixture file containing ASCII "0123456789" (10 bytes). Used by the Archive
    helpers to exercise `fileSize = 10`. -/
private def writeDigitsFile : IO System.FilePath := do
  let path : System.FilePath := "/tmp/lean-zlib-bounded-digits.bin"
  IO.FS.writeBinFile path "0123456789".toUTF8
  return path

/-- `Archive.readBoundedSpanFromHandle`: valid span + sufficient data, and
    offset-past-fileSize failure surfacing the `"exceeds file size"` substring,
    and overshooting-span failure surfacing `"extends past end of file"`. -/
private def testReadBoundedSpanFromHandle : IO Unit := do
  let path ← writeDigitsFile
  -- Happy path: read 4 bytes from offset 2 (= "2345")
  IO.FS.withFile path .read fun h => do
    let buf ← Archive.readBoundedSpanFromHandle h 10 2 4 "digits mid-span"
    unless buf.data == "2345".toUTF8.data do
      throw (IO.userError s!"readBoundedSpanFromHandle: expected \"2345\", got {String.fromUTF8! buf}")
  -- Failure: offset beyond fileSize → "exceeds file size"
  assertThrows "readBoundedSpanFromHandle offset>fileSize"
    (IO.FS.withFile path .read fun h => do
      let _ ← Archive.readBoundedSpanFromHandle h 10 11 1 "digits past eof"
      pure ())
    "exceeds file size"
  -- Failure: span runs past the tail → "extends past end of file"
  assertThrows "readBoundedSpanFromHandle span>tail"
    (IO.FS.withFile path .read fun h => do
      let _ ← Archive.readBoundedSpanFromHandle h 10 8 5 "digits overshoot"
      pure ())
    "extends past end of file"

/-- `Archive.readBoundedExactFromHandle`: valid post-seek read, and short-read
    failure surfacing the `"short read for"` substring sourced from `readExact`. -/
private def testReadBoundedExactFromHandle : IO Unit := do
  let path ← writeDigitsFile
  -- Happy path: caller seeks, then reads exactly 3 bytes (= "234")
  IO.FS.withFile path .read fun h => do
    Handle.seek h 2
    let buf ← Archive.readBoundedExactFromHandle h 3 "digits post-seek"
    unless buf.data == "234".toUTF8.data do
      throw (IO.userError s!"readBoundedExactFromHandle: expected \"234\", got {String.fromUTF8! buf}")
  -- Failure: caller requests more bytes than the handle has remaining
  assertThrows "readBoundedExactFromHandle short-read"
    (IO.FS.withFile path .read fun h => do
      Handle.seek h 8
      let _ ← Archive.readBoundedExactFromHandle h 5 "digits short"
      pure ())
    "short read for"

/-- `Tar.readBoundedExactFromStream`: valid stream read, and addressable-range
    failure surfacing the `"exceeds addressable range"` substring. -/
private def testReadBoundedExactFromStream : IO Unit := do
  let stream ← byteArrayReadStream "abcdef".toUTF8
  -- Happy path: pull 4 bytes from the stream
  let buf ← Tar.readBoundedExactFromStream stream 4 "alpha"
  unless buf.data == "abcd".toUTF8.data do
    throw (IO.userError s!"readBoundedExactFromStream: expected \"abcd\", got {String.fromUTF8! buf}")
  -- Failure: length exceeds USize addressable range. On a 64-bit host
  -- `USize.size = 2^64`, so any `Nat ≥ USize.size` trips the guard. We use
  -- `USize.size` directly to stay portable to the (currently hypothetical)
  -- 32-bit build.
  let stream2 ← byteArrayReadStream "abcdef".toUTF8
  assertThrows "readBoundedExactFromStream addressable-range"
    (do
      let _ ← Tar.readBoundedExactFromStream stream2 USize.size "alpha overflow"
      pure ())
    "exceeds addressable range"

/-- `Tar.readBoundedEntryData`: happy path reads a small payload inside the cap,
    and over-the-cap call surfaces the `"exceeds maximum"` substring. -/
private def testReadBoundedEntryData : IO Unit := do
  -- Construct a 16-byte payload followed by enough padding to reach the next
  -- 512-byte boundary, since `readEntryData` also consumes the tar padding.
  let payload : ByteArray := (ByteArray.mk (Array.replicate 16 0x41)) ++
    (ByteArray.mk (Array.replicate (512 - 16) 0))
  let stream ← byteArrayReadStream payload
  -- Happy path: 16 ≤ maxSize = 1024, payload buffered into memory.
  let buf ← Tar.readBoundedEntryData stream 16 1024 "payload"
  unless buf.size == 16 do
    throw (IO.userError s!"readBoundedEntryData: expected 16 bytes, got {buf.size}")
  -- Failure: size exceeds caller-supplied max.
  let stream2 ← byteArrayReadStream payload
  assertThrows "readBoundedEntryData exceeds-maximum"
    (do
      let _ ← Tar.readBoundedEntryData stream2 16 8 "payload overflow"
      pure ())
    "exceeds maximum"

/-- Sanity checks for the P5.2 pure `Archive.SpanInFile` predicate. Concrete
    `UInt64` triples kernel-evaluate via `decide`. -/
example : Archive.SpanInFile 100 10 20 := by decide
example : ¬ Archive.SpanInFile 100 90 20 := by decide
example : ¬ Archive.SpanInFile 100 200 0 := by decide
example : Archive.SpanInFile 100 0 0 := by decide
example : Archive.SpanInFile 100 100 0 := by decide

def tests : IO Unit := do
  testReadBoundedSpanFromHandle
  testReadBoundedExactFromHandle
  testReadBoundedExactFromStream
  testReadBoundedEntryData
  IO.println "bounded-read helper tests passed"

end ZipTest.BoundedRead
