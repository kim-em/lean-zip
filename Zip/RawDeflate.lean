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
    `maxDecompressedSize` limits output size (0 = no limit). -/
@[extern "lean_raw_deflate_decompress"]
opaque decompress (data : @& ByteArray) (maxDecompressedSize : UInt64 := 0) : IO ByteArray

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

/-- Decompress raw deflate data from input stream to output stream. -/
partial def decompressStream (input : IO.FS.Stream) (output : IO.FS.Stream) : IO Unit := do
  let state ← InflateState.new
  repeat do
    let chunk ← input.read 65536
    if chunk.isEmpty then break
    let decompressed ← state.push chunk
    if decompressed.size > 0 then output.write decompressed
  let final ← state.finish
  if final.size > 0 then output.write final
  output.flush

end RawDeflate
