import Zip.Gzip

/-! FFI bindings for raw DEFLATE compression/decompression (no framing headers),
    used by ZIP archives (method 8). -/

namespace RawDeflate

/-- Compress data using raw deflate (no header/trailer).
    This is the format used by ZIP archives (method 8).
    `level` ranges from 0 (no compression) to 9 (best compression), default 6. -/
@[extern "lean_raw_deflate_compress"]
opaque compress (data : @& ByteArray) (level : UInt8 := 6) : IO ByteArray

/-- Decompress raw deflate data.
    `maxDecompressedSize` caps output size; default 1 GiB; pass `0` to opt
    into unlimited mode (bomb-unsafe for untrusted input). Overflow raises
    `IO.userError` containing `"decompressed size exceeds limit"`.
    See `SECURITY_INVENTORY.md` *Decompression Limit Inventory*. -/
@[extern "lean_raw_deflate_decompress"]
opaque decompress (data : @& ByteArray)
    (maxDecompressedSize : UInt64 := 1024 * 1024 * 1024) : IO ByteArray

-- Streaming raw deflate. Reuses Gzip.DeflateState/InflateState types
-- since the underlying z_stream state is format-agnostic after init.
-- Use state.push and state.finish from the Gzip module.

/-- Create a new streaming raw deflate compressor. -/
@[extern "lean_raw_deflate_new"]
opaque DeflateState.new (level : UInt8 := 6) : IO Gzip.DeflateState

/-- Create a new streaming raw deflate decompressor. -/
@[extern "lean_raw_inflate_new"]
opaque InflateState.new : IO Gzip.InflateState

/-- Compress from input stream to output stream using raw deflate. -/
partial def compressStream (input : IO.FS.Stream) (output : IO.FS.Stream)
    (level : UInt8 := 6) : IO Unit := do
  let state ← DeflateState.new level
  repeat do
    let chunk ← input.read 65536
    if chunk.isEmpty then break
    let compressed ← state.push chunk
    if compressed.size > 0 then output.write compressed
  let final ← state.finish
  if final.size > 0 then output.write final
  output.flush

/-- Decompress raw deflate data from input stream to output stream.
    Input memory usage is bounded. `maxDecompressedSize` caps the *total*
    output bytes written to `output`; default `0` means unlimited
    (bomb-unsafe for untrusted input). Overflow raises `IO.userError`
    containing `"exceeds limit"` (full message:
    `"raw deflate: decompressed stream exceeds limit (<N> bytes)"`) and
    aborts before writing the overflowing chunk, so the already-written
    prefix is at most `maxDecompressedSize` bytes.
    See `SECURITY_INVENTORY.md` *Decompression Limit Inventory*. -/
partial def decompressStream (input : IO.FS.Stream) (output : IO.FS.Stream)
    (maxDecompressedSize : UInt64 := 0) : IO Unit := do
  let state ← InflateState.new
  let totalRef ← IO.mkRef (0 : UInt64)
  let checkAndWrite (chunk : ByteArray) : IO Unit := do
    if chunk.size > 0 then
      let total ← totalRef.get
      let next := total + chunk.size.toUInt64
      if maxDecompressedSize ≠ 0 && next > maxDecompressedSize then
        throw (IO.userError
          s!"raw deflate: decompressed stream exceeds limit ({maxDecompressedSize} bytes)")
      totalRef.set next
      output.write chunk
  repeat do
    let chunk ← input.read 65536
    if chunk.isEmpty then break
    let decompressed ← state.push chunk
    checkAndWrite decompressed
  let final ← state.finish
  checkAndWrite final
  output.flush

end RawDeflate
