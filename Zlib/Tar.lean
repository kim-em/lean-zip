import Zlib.Binary
import Zlib.Gzip

namespace Tar

/-- Tar entry metadata. -/
structure Entry where
  path     : String
  size     : UInt64   := 0
  mode     : UInt32   := 0o644
  mtime    : UInt64   := 0
  uid      : UInt32   := 0
  gid      : UInt32   := 0
  typeflag : UInt8    := 0x30  -- '0' = regular file
  linkname : String   := ""
  uname    : String   := ""
  gname    : String   := ""
  deriving Repr, Inhabited

/-- Typeflag for regular file. -/
def typeRegular : UInt8 := 0x30  -- '0'
/-- Typeflag for directory. -/
def typeDirectory : UInt8 := 0x35  -- '5'

-- UStar header field offsets and sizes
private def hdrName     := (0, 100)
private def hdrMode     := (100, 8)
private def hdrUid      := (108, 8)
private def hdrGid      := (116, 8)
private def hdrSize     := (124, 12)
private def hdrMtime    := (136, 12)
private def hdrChksum   := (148, 8)
private def hdrTypeflag := (156, 1)
private def hdrLinkname := (157, 100)
private def hdrMagic    := (257, 6)
private def hdrVersion  := (263, 2)
private def hdrUname    := (265, 32)
private def hdrGname    := (297, 32)
private def hdrPrefix   := (345, 155)

/-- Split a path into (prefix, name) for UStar format.
    Returns `none` if the path is too long to encode. -/
def splitPath (path : String) : Option (String × String) := Id.run do
  if path.utf8ByteSize <= 100 then
    return some ("", path)
  -- Find last '/' that gives name <= 100 and prefix <= 155
  let bytes := path.toUTF8
  let mut bestSplit : Option Nat := none
  for i in [:bytes.size] do
    if bytes[i]! == '/'.toNat.toUInt8 then
      let nameLen := bytes.size - i - 1
      let pfxLen := i
      if nameLen <= 100 && pfxLen <= 155 then
        bestSplit := some i
  match bestSplit with
  | some i =>
    let pfx := String.fromUTF8! (bytes.extract 0 i)
    let name := String.fromUTF8! (bytes.extract (i + 1) bytes.size)
    return some (pfx, name)
  | none => return none

/-- Compute tar checksum: sum all 512 bytes, treating bytes 148..155 as spaces. -/
@[noinline] def computeChecksum (header : ByteArray) : UInt32 := Id.run do
  let mut sum : UInt32 := 0
  for i in [:512] do
    if i >= 148 && i < 156 then
      sum := sum + ' '.toNat.toUInt32
    else
      sum := sum + (header[i]!).toUInt32
  return sum

/-- Build a 512-byte UStar header. -/
def buildHeader (entry : Entry) : IO ByteArray := do
  let some (pfx, name) := splitPath entry.path
    | throw (IO.userError s!"tar: path too long: {entry.path}")
  -- Start with 512 zero bytes
  let mut hdr := Binary.zeros 512
  -- Helper to write into the header at a given offset
  let writeField (hdr : ByteArray) (offset : Nat) (field : ByteArray) : ByteArray := Id.run do
    let mut h := hdr
    for i in [:field.size] do
      h := h.set! (offset + i) field[i]!
    return h
  -- Write fields
  hdr := writeField hdr hdrName.1 (Binary.writeString name hdrName.2)
  hdr := writeField hdr hdrMode.1 (Binary.writeOctal entry.mode.toUInt64 hdrMode.2)
  hdr := writeField hdr hdrUid.1 (Binary.writeOctal entry.uid.toUInt64 hdrUid.2)
  hdr := writeField hdr hdrGid.1 (Binary.writeOctal entry.gid.toUInt64 hdrGid.2)
  hdr := writeField hdr hdrSize.1 (Binary.writeOctal entry.size hdrSize.2)
  hdr := writeField hdr hdrMtime.1 (Binary.writeOctal entry.mtime hdrMtime.2)
  -- Checksum field: fill with spaces for now
  for i in [:8] do
    hdr := hdr.set! (hdrChksum.1 + i) ' '.toNat.toUInt8
  -- Typeflag
  hdr := hdr.set! hdrTypeflag.1 entry.typeflag
  -- Linkname
  hdr := writeField hdr hdrLinkname.1 (Binary.writeString entry.linkname hdrLinkname.2)
  -- Magic and version
  hdr := writeField hdr hdrMagic.1 "ustar\x00".toUTF8
  hdr := writeField hdr hdrVersion.1 "00".toUTF8
  -- Uname/gname
  hdr := writeField hdr hdrUname.1 (Binary.writeString entry.uname hdrUname.2)
  hdr := writeField hdr hdrGname.1 (Binary.writeString entry.gname hdrGname.2)
  -- Prefix
  hdr := writeField hdr hdrPrefix.1 (Binary.writeString pfx hdrPrefix.2)
  -- Compute and write checksum
  let chksum := computeChecksum hdr
  let chksumBytes := Binary.writeOctal chksum.toUInt64 7 ++ ByteArray.mk #[' '.toNat.toUInt8]
  hdr := writeField hdr hdrChksum.1 chksumBytes
  return hdr

/-- Parse a 512-byte header block into an Entry. Returns `none` for zero blocks. -/
def parseHeader (block : ByteArray) : Option Entry := Id.run do
  -- Check for zero block (end of archive)
  let mut allZero := true
  for i in [:512] do
    if block[i]! != 0 then
      allZero := false
      break
  if allZero then return none
  let name := Binary.readString block hdrName.1 hdrName.2
  let pfx := Binary.readString block hdrPrefix.1 hdrPrefix.2
  let fullPath := if pfx.isEmpty then name else pfx ++ "/" ++ name
  some {
    path := fullPath
    size := Binary.readOctal block hdrSize.1 hdrSize.2
    mode := (Binary.readOctal block hdrMode.1 hdrMode.2).toUInt32
    mtime := Binary.readOctal block hdrMtime.1 hdrMtime.2
    uid := (Binary.readOctal block hdrUid.1 hdrUid.2).toUInt32
    gid := (Binary.readOctal block hdrGid.1 hdrGid.2).toUInt32
    typeflag := block[hdrTypeflag.1]!
    linkname := Binary.readString block hdrLinkname.1 hdrLinkname.2
    uname := Binary.readString block hdrUname.1 hdrUname.2
    gname := Binary.readString block hdrGname.1 hdrGname.2
  }

/-- Compute padding needed to reach next 512-byte boundary. -/
def paddingFor (size : UInt64) : Nat :=
  let rem := size.toNat % 512
  if rem == 0 then 0 else 512 - rem

/-- Create a tar archive from files, writing to output stream.
    `basePath` is stripped from file paths in the archive. -/
partial def create (output : IO.FS.Stream) (basePath : System.FilePath)
    (files : Array System.FilePath) : IO Unit := do
  let baseStr := basePath.toString
  for file in files do
    let fmeta ← file.metadata
    let fileStr := file.toString
    let relPath :=
      if fileStr.startsWith baseStr then
        let stripped := (fileStr.drop baseStr.length).toString
        if stripped.startsWith "/" then (stripped.drop 1).toString else stripped
      else fileStr
    if relPath.isEmpty then continue
    let isDir := fmeta.type == .dir
    let entry : Entry := {
      path := if isDir && !relPath.endsWith "/" then relPath ++ "/" else relPath
      size := if isDir then 0 else fmeta.byteSize
      mtime := fmeta.modified.sec.toNat.toUInt64
      mode := if isDir then 0o755 else 0o644
      typeflag := if isDir then typeDirectory else typeRegular
    }
    let header ← buildHeader entry
    output.write header
    if !isDir then
      IO.FS.withFile file .read fun h => do
        let mut remaining := entry.size.toNat
        while remaining > 0 do
          let toRead := min remaining 65536
          let chunk ← h.read toRead.toUSize
          if chunk.isEmpty then break
          output.write chunk
          remaining := remaining - chunk.size
      let pad := paddingFor entry.size
      if pad > 0 then
        output.write (Binary.zeros pad)
  -- End of archive: two 512-byte zero blocks
  output.write (Binary.zeros 1024)
  output.flush

/-- Create a tar archive from all files under a directory. -/
partial def createFromDir (output : IO.FS.Stream) (dir : System.FilePath) : IO Unit := do
  let files ← dir.walkDir
  -- Sort for deterministic order
  let sorted := files.insertionSort (·.toString < ·.toString)
  create output dir sorted

/-- Extract a tar archive from input stream to output directory. -/
partial def extract (input : IO.FS.Stream) (outDir : System.FilePath) : IO Unit := do
  let outDirStr := outDir.toString
  repeat do
    let block ← input.read 512
    if block.size < 512 then break
    match parseHeader block with
    | none => break
    | some entry =>
      let outPath := outDir / entry.path
      -- Path safety: check for directory traversal
      let resolved := outPath.toString
      unless resolved.startsWith outDirStr do
        throw (IO.userError s!"tar: path escapes output directory: {entry.path}")
      if entry.typeflag == typeDirectory then
        IO.FS.createDirAll outPath
      else
        if let some parent := outPath.parent then
          IO.FS.createDirAll parent
        IO.FS.withFile outPath .write fun h => do
          let mut remaining := entry.size.toNat
          while remaining > 0 do
            let toRead := min remaining 65536
            let chunk ← input.read toRead.toUSize
            if chunk.isEmpty then break
            h.write chunk
            remaining := remaining - chunk.size
        let pad := paddingFor entry.size
        if pad > 0 then
          let _ ← input.read pad.toUSize

/-- List entries in a tar archive without extracting. -/
partial def list (input : IO.FS.Stream) : IO (Array Entry) := do
  let mut entries := #[]
  repeat do
    let block ← input.read 512
    if block.size < 512 then break
    match parseHeader block with
    | none => break
    | some entry =>
      entries := entries.push entry
      -- Skip past file data + padding
      let dataSize := entry.size.toNat + paddingFor entry.size
      let mut skipped := 0
      while skipped < dataSize do
        let toRead := min (dataSize - skipped) 65536
        let chunk ← input.read toRead.toUSize
        if chunk.isEmpty then break
        skipped := skipped + chunk.size
  return entries

-- .tar.gz composition

/-- Create a .tar.gz archive from a directory.
    True streaming — bounded memory regardless of archive size. -/
partial def createTarGz (outputPath : System.FilePath) (dir : System.FilePath)
    (level : UInt8 := 6) : IO Unit := do
  IO.FS.withFile outputPath .write fun outH => do
    let outStream := IO.FS.Stream.ofHandle outH
    let deflate ← Gzip.DeflateState.new level
    -- Custom stream that compresses writes through gzip
    let tarStream : IO.FS.Stream := {
      flush := pure ()
      read := fun _ => pure ByteArray.empty
      write := fun chunk => do
        let compressed ← deflate.push chunk
        if compressed.size > 0 then outStream.write compressed
      getLine := pure ""
      putStr := fun _ => pure ()
      isTty := pure false
    }
    createFromDir tarStream dir
    let final ← deflate.finish
    if final.size > 0 then outStream.write final
    outStream.flush

/-- Extract a .tar.gz archive.
    True streaming — bounded memory regardless of archive size. -/
partial def extractTarGz (inputPath : System.FilePath) (outDir : System.FilePath) : IO Unit := do
  IO.FS.withFile inputPath .read fun inH => do
    let inStream := IO.FS.Stream.ofHandle inH
    let inflate ← Gzip.InflateState.new
    let bufRef ← IO.mkRef ByteArray.empty
    -- Custom stream that decompresses reads through gzip
    let tarStream : IO.FS.Stream := {
      flush := pure ()
      read := fun n => do
        let mut buf ← bufRef.get
        while buf.size < n.toNat do
          let compressed ← inStream.read 65536
          if compressed.isEmpty then
            -- Try to finish inflate for any remaining data
            let final ← inflate.finish
            if final.size > 0 then buf := buf ++ final
            break
          let decompressed ← inflate.push compressed
          buf := buf ++ decompressed
        let toReturn := min buf.size n.toNat
        let result := buf.extract 0 toReturn
        bufRef.set (buf.extract toReturn buf.size)
        return result
      write := fun _ => pure ()
      getLine := pure ""
      putStr := fun _ => pure ()
      isTty := pure false
    }
    extract tarStream outDir

end Tar
