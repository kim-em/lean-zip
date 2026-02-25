/-! FFI bindings for gzip compression/decompression (RFC 1952).
    Supports concatenated streams, format auto-detection, and streaming I/O. -/
namespace Gzip

/-- Compress data in gzip format (with gzip header/trailer, compatible with `gzip`/`gunzip`).
    `level` ranges from 0 (no compression) to 9 (best compression), default 6. -/
@[extern "lean_gzip_compress"]
opaque compress (data : @& ByteArray) (level : UInt8 := 6) : IO ByteArray

/-- Decompress gzip data. Also handles concatenated gzip streams and raw zlib data.
    `maxDecompressedSize` limits output size (0 = no limit). -/
@[extern "lean_gzip_decompress"]
opaque decompress (data : @& ByteArray) (maxDecompressedSize : UInt64 := 0) : IO ByteArray

-- Streaming compression

/-- Opaque streaming gzip compression state. Automatically cleaned up when dropped. -/
opaque DeflateState.nonemptyType : NonemptyType
def DeflateState : Type := DeflateState.nonemptyType.type
instance : Nonempty DeflateState := DeflateState.nonemptyType.property

/-- Create a new streaming gzip compressor. -/
@[extern "lean_gzip_deflate_new"]
opaque DeflateState.new (level : UInt8 := 6) : IO DeflateState

/-- Push a chunk of uncompressed data through the compressor. Returns compressed output. -/
@[extern "lean_gzip_deflate_push"]
opaque DeflateState.push (state : @& DeflateState) (chunk : @& ByteArray) : IO ByteArray

/-- Finish the compression stream. Returns any remaining compressed data
    (gzip trailer, etc.). Must be called exactly once after all data has been pushed. -/
@[extern "lean_gzip_deflate_finish"]
opaque DeflateState.finish (state : @& DeflateState) : IO ByteArray

-- Streaming decompression

/-- Opaque streaming gzip decompression state. Automatically cleaned up when dropped. -/
opaque InflateState.nonemptyType : NonemptyType
def InflateState : Type := InflateState.nonemptyType.type
instance : Nonempty InflateState := InflateState.nonemptyType.property

/-- Create a new streaming gzip decompressor. Auto-detects gzip and zlib formats. -/
@[extern "lean_gzip_inflate_new"]
opaque InflateState.new : IO InflateState

/-- Push a chunk of compressed data through the decompressor. Returns decompressed output.
    Handles concatenated gzip streams. -/
@[extern "lean_gzip_inflate_push"]
opaque InflateState.push (state : @& InflateState) (chunk : @& ByteArray) : IO ByteArray

/-- Finish the decompression stream and clean up. -/
@[extern "lean_gzip_inflate_finish"]
opaque InflateState.finish (state : @& InflateState) : IO ByteArray

-- Stream piping

/-- Compress from input stream to output stream in gzip format.
    Reads 64KB chunks — memory usage is bounded regardless of data size. -/
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

/-- Decompress gzip data from input stream to output stream.
    Handles concatenated gzip streams. Memory usage is bounded. -/
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

-- File helpers

/-- Compress a file to gzip format, writing to `path ++ ".gz"`.
    Returns the output path. Streams with bounded memory. -/
def compressFile (path : System.FilePath) (level : UInt8 := 6) : IO System.FilePath := do
  let outPath : System.FilePath := ⟨path.toString ++ ".gz"⟩
  IO.FS.withFile path .read fun inH =>
    IO.FS.withFile outPath .write fun outH =>
      compressStream (IO.FS.Stream.ofHandle inH) (IO.FS.Stream.ofHandle outH) level
  return outPath

/-- Decompress a gzip file. Strips `.gz` suffix, or appends `.ungz` as fallback.
    Optional explicit output path. Streams with bounded memory. -/
def decompressFile (path : System.FilePath) (outPath : Option System.FilePath := none)
    : IO System.FilePath := do
  let out := match outPath with
    | some p => p
    | none =>
      let s := path.toString
      if s.endsWith ".gz" then ⟨(s.dropEnd 3).toString⟩ else ⟨s ++ ".ungz"⟩
  IO.FS.withFile path .read fun inH =>
    IO.FS.withFile out .write fun outH =>
      decompressStream (IO.FS.Stream.ofHandle inH) (IO.FS.Stream.ofHandle outH)
  return out

end Gzip
