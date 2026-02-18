namespace Zstd

/-- Compress data in Zstandard format.
    `level` ranges from 1 (fastest) to 22 (best compression), default 3. -/
@[extern "lean_zstd_compress"]
opaque compress (data : @& ByteArray) (level : UInt8 := 3) : IO ByteArray

/-- Decompress Zstandard data. -/
@[extern "lean_zstd_decompress"]
opaque decompress (data : @& ByteArray) : IO ByteArray

-- Streaming compression

/-- Opaque streaming Zstd compression state. Automatically cleaned up when dropped. -/
opaque CompressState.nonemptyType : NonemptyType
def CompressState : Type := CompressState.nonemptyType.type
instance : Nonempty CompressState := CompressState.nonemptyType.property

/-- Create a new streaming Zstd compressor. -/
@[extern "lean_zstd_compress_new"]
opaque CompressState.new (level : UInt8 := 3) : IO CompressState

/-- Push a chunk of uncompressed data through the compressor. Returns compressed output. -/
@[extern "lean_zstd_compress_push"]
opaque CompressState.push (state : @& CompressState) (chunk : @& ByteArray) : IO ByteArray

/-- Finish the compression stream. Returns any remaining compressed data.
    Must be called exactly once after all data has been pushed. -/
@[extern "lean_zstd_compress_finish"]
opaque CompressState.finish (state : @& CompressState) : IO ByteArray

-- Streaming decompression

/-- Opaque streaming Zstd decompression state. Automatically cleaned up when dropped. -/
opaque DecompressState.nonemptyType : NonemptyType
def DecompressState : Type := DecompressState.nonemptyType.type
instance : Nonempty DecompressState := DecompressState.nonemptyType.property

/-- Create a new streaming Zstd decompressor. -/
@[extern "lean_zstd_decompress_new"]
opaque DecompressState.new : IO DecompressState

/-- Push a chunk of compressed data through the decompressor. Returns decompressed output. -/
@[extern "lean_zstd_decompress_push"]
opaque DecompressState.push (state : @& DecompressState) (chunk : @& ByteArray) : IO ByteArray

/-- Finish the decompression stream and clean up. -/
@[extern "lean_zstd_decompress_finish"]
opaque DecompressState.finish (state : @& DecompressState) : IO ByteArray

-- Stream piping

/-- Compress from input stream to output stream in Zstd format.
    Reads 64KB chunks — memory usage is bounded regardless of data size. -/
partial def compressStream (input : IO.FS.Stream) (output : IO.FS.Stream)
    (level : UInt8 := 3) : IO Unit := do
  let state ← CompressState.new level
  repeat do
    let chunk ← input.read 65536
    if chunk.isEmpty then break
    let compressed ← state.push chunk
    if compressed.size > 0 then output.write compressed
  let final ← state.finish
  if final.size > 0 then output.write final
  output.flush

/-- Decompress Zstd data from input stream to output stream. Memory usage is bounded. -/
partial def decompressStream (input : IO.FS.Stream) (output : IO.FS.Stream) : IO Unit := do
  let state ← DecompressState.new
  repeat do
    let chunk ← input.read 65536
    if chunk.isEmpty then break
    let decompressed ← state.push chunk
    if decompressed.size > 0 then output.write decompressed
  let final ← state.finish
  if final.size > 0 then output.write final
  output.flush

/-- Compress a file in Zstd format. Output goes to `inputPath ++ ".zst"`. -/
partial def compressFile (inputPath : System.FilePath) (level : UInt8 := 3) : IO Unit := do
  let outputPath : System.FilePath := inputPath.toString ++ ".zst"
  IO.FS.withFile inputPath .read fun inH =>
    IO.FS.withFile outputPath .write fun outH =>
      compressStream (IO.FS.Stream.ofHandle inH) (IO.FS.Stream.ofHandle outH) level

/-- Decompress a `.zst` file. If the path ends in `.zst`, output strips the extension;
    otherwise appends `.unzst`. -/
partial def decompressFile (inputPath : System.FilePath) : IO Unit := do
  let inputStr := inputPath.toString
  let outputPath : System.FilePath :=
    if inputStr.endsWith ".zst" then
      (inputStr.dropEnd 4).toString
    else
      inputStr ++ ".unzst"
  IO.FS.withFile inputPath .read fun inH =>
    IO.FS.withFile outputPath .write fun outH =>
      decompressStream (IO.FS.Stream.ofHandle inH) (IO.FS.Stream.ofHandle outH)

end Zstd
