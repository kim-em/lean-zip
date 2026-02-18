import Zlib.Binary
import Zlib.Checksum
import Zlib.RawDeflate

namespace Zip

-- ZIP signatures
private def sigLocal    : UInt32 := 0x04034b50
private def sigCentral  : UInt32 := 0x02014b50
private def sigEOCD     : UInt32 := 0x06054b50

/-- ZIP entry metadata. -/
structure Entry where
  path             : String
  compressedSize   : UInt32 := 0
  uncompressedSize : UInt32 := 0
  crc32            : UInt32 := 0
  method           : UInt16 := 0  -- 0 = stored, 8 = deflated
  localOffset      : UInt32 := 0
  deriving Repr, Inhabited

-- DOS date/time encoding (minimal: default to 1980-01-01 00:00:00)
private def defaultDosTime : UInt16 := 0
private def defaultDosDate : UInt16 := 0x0021  -- 1980-01-01

/-- Write a local file header. Returns the header bytes. -/
private def writeLocalHeader (entry : Entry) : ByteArray := Id.run do
  let nameBytes := entry.path.toUTF8
  let mut buf := ByteArray.empty
  -- Signature
  buf := buf ++ Binary.writeUInt32LE sigLocal
  -- Version needed (2.0 = 20)
  buf := buf ++ Binary.writeUInt16LE 20
  -- General purpose bit flag
  buf := buf ++ Binary.writeUInt16LE 0
  -- Compression method
  buf := buf ++ Binary.writeUInt16LE entry.method
  -- Last mod time / date
  buf := buf ++ Binary.writeUInt16LE defaultDosTime
  buf := buf ++ Binary.writeUInt16LE defaultDosDate
  -- CRC-32
  buf := buf ++ Binary.writeUInt32LE entry.crc32
  -- Compressed size
  buf := buf ++ Binary.writeUInt32LE entry.compressedSize
  -- Uncompressed size
  buf := buf ++ Binary.writeUInt32LE entry.uncompressedSize
  -- File name length
  buf := buf ++ Binary.writeUInt16LE nameBytes.size.toUInt16
  -- Extra field length
  buf := buf ++ Binary.writeUInt16LE 0
  -- File name
  buf := buf ++ nameBytes
  return buf

/-- Write a central directory header. Returns the header bytes. -/
private def writeCentralHeader (entry : Entry) : ByteArray := Id.run do
  let nameBytes := entry.path.toUTF8
  let mut buf := ByteArray.empty
  -- Signature
  buf := buf ++ Binary.writeUInt32LE sigCentral
  -- Version made by (2.0 = 20, Unix = 3)
  buf := buf ++ Binary.writeUInt16LE (3 * 256 + 20)
  -- Version needed
  buf := buf ++ Binary.writeUInt16LE 20
  -- General purpose bit flag
  buf := buf ++ Binary.writeUInt16LE 0
  -- Compression method
  buf := buf ++ Binary.writeUInt16LE entry.method
  -- Last mod time / date
  buf := buf ++ Binary.writeUInt16LE defaultDosTime
  buf := buf ++ Binary.writeUInt16LE defaultDosDate
  -- CRC-32
  buf := buf ++ Binary.writeUInt32LE entry.crc32
  -- Compressed size
  buf := buf ++ Binary.writeUInt32LE entry.compressedSize
  -- Uncompressed size
  buf := buf ++ Binary.writeUInt32LE entry.uncompressedSize
  -- File name length
  buf := buf ++ Binary.writeUInt16LE nameBytes.size.toUInt16
  -- Extra field length
  buf := buf ++ Binary.writeUInt16LE 0
  -- File comment length
  buf := buf ++ Binary.writeUInt16LE 0
  -- Disk number start
  buf := buf ++ Binary.writeUInt16LE 0
  -- Internal file attributes
  buf := buf ++ Binary.writeUInt16LE 0
  -- External file attributes
  buf := buf ++ Binary.writeUInt32LE 0
  -- Relative offset of local header
  buf := buf ++ Binary.writeUInt32LE entry.localOffset
  -- File name
  buf := buf ++ nameBytes
  return buf

/-- Write the end of central directory record. -/
private def writeEOCD (numEntries : UInt16) (cdSize cdOffset : UInt32) : ByteArray := Id.run do
  let mut buf := ByteArray.empty
  buf := buf ++ Binary.writeUInt32LE sigEOCD
  -- Disk number
  buf := buf ++ Binary.writeUInt16LE 0
  -- Disk with CD start
  buf := buf ++ Binary.writeUInt16LE 0
  -- Number of entries on this disk
  buf := buf ++ Binary.writeUInt16LE numEntries
  -- Total number of entries
  buf := buf ++ Binary.writeUInt16LE numEntries
  -- Size of central directory
  buf := buf ++ Binary.writeUInt32LE cdSize
  -- Offset of start of central directory
  buf := buf ++ Binary.writeUInt32LE cdOffset
  -- Comment length
  buf := buf ++ Binary.writeUInt16LE 0
  return buf

/-- Create a ZIP archive from (archivePath, diskPath) pairs. -/
def create (outputPath : System.FilePath)
    (files : Array (String × System.FilePath)) : IO Unit := do
  let mut entries : Array Entry := #[]
  let mut offset : UInt32 := 0
  let mut body := ByteArray.empty
  for (archiveName, diskPath) in files do
    let fileData ← IO.FS.readBinFile diskPath
    let crc ← Checksum.crc32 0 fileData
    -- Try deflating; use stored if deflate isn't smaller
    let deflated ← RawDeflate.compress fileData
    let useDeflate := deflated.size < fileData.size
    let method : UInt16 := if useDeflate then 8 else 0
    let compData := if useDeflate then deflated else fileData
    let entry : Entry := {
      path := archiveName
      compressedSize := compData.size.toUInt32
      uncompressedSize := fileData.size.toUInt32
      crc32 := crc
      method := method
      localOffset := offset
    }
    entries := entries.push entry
    let localHdr := writeLocalHeader entry
    body := body ++ localHdr ++ compData
    offset := offset + localHdr.size.toUInt32 + compData.size.toUInt32
  -- Build central directory
  let cdOffset := offset
  let mut cd := ByteArray.empty
  for entry in entries do
    cd := cd ++ writeCentralHeader entry
  -- Write EOCD
  let eocd := writeEOCD entries.size.toUInt16 cd.size.toUInt32 cdOffset
  IO.FS.writeBinFile outputPath (body ++ cd ++ eocd)

/-- Create a ZIP archive from all files under a directory. -/
partial def createFromDir (outputPath : System.FilePath) (dir : System.FilePath) : IO Unit := do
  let allFiles ← dir.walkDir
  let sorted := allFiles.insertionSort (·.toString < ·.toString)
  let dirStr := dir.toString
  let mut pairs : Array (String × System.FilePath) := #[]
  for file in sorted do
    let fmeta ← file.metadata
    if fmeta.type == .dir then continue  -- ZIP doesn't need directory entries for extraction
    let fileStr := file.toString
    let relPath :=
      if fileStr.startsWith dirStr then
        let stripped := (fileStr.drop dirStr.length).toString
        if stripped.startsWith "/" then (stripped.drop 1).toString else stripped
      else fileStr
    if relPath.isEmpty then continue
    pairs := pairs.push (relPath, file)
  create outputPath pairs

/-- Find the EOCD record in a ZIP file. Searches backwards from end. -/
private def findEOCD (data : ByteArray) : Option Nat := Id.run do
  -- EOCD is at least 22 bytes, search backwards for signature
  if data.size < 22 then return none
  let mut i := data.size - 22
  -- Search up to 65557 bytes back (max comment length = 65535 + 22)
  let minPos := if data.size > 65557 then data.size - 65557 else 0
  while i >= minPos do
    if Binary.readUInt32LE data i == sigEOCD then
      return some i
    if i == 0 then break
    i := i - 1
  return none

/-- Parse central directory entries from a ZIP file. -/
private def parseCentralDir (data : ByteArray) (cdOffset cdSize : Nat) : Array Entry := Id.run do
  let mut entries : Array Entry := #[]
  let mut pos := cdOffset
  let cdEnd := cdOffset + cdSize
  while pos + 46 <= cdEnd do
    let sig := Binary.readUInt32LE data pos
    if sig != sigCentral then break
    let method := Binary.readUInt16LE data (pos + 10)
    let crc := Binary.readUInt32LE data (pos + 16)
    let compSize := Binary.readUInt32LE data (pos + 20)
    let uncompSize := Binary.readUInt32LE data (pos + 24)
    let nameLen := (Binary.readUInt16LE data (pos + 28)).toNat
    let extraLen := (Binary.readUInt16LE data (pos + 30)).toNat
    let commentLen := (Binary.readUInt16LE data (pos + 32)).toNat
    let localOffset := Binary.readUInt32LE data (pos + 42)
    let nameBytes := data.extract (pos + 46) (pos + 46 + nameLen)
    let name := String.fromUTF8! nameBytes
    entries := entries.push {
      path := name
      compressedSize := compSize
      uncompressedSize := uncompSize
      crc32 := crc
      method := method
      localOffset := localOffset
    }
    pos := pos + 46 + nameLen + extraLen + commentLen
  return entries

/-- List entries in a ZIP archive. -/
def list (inputPath : System.FilePath) : IO (Array Entry) := do
  let data ← IO.FS.readBinFile inputPath
  let some eocdPos := findEOCD data
    | throw (IO.userError "zip: cannot find end of central directory")
  let cdSize := (Binary.readUInt32LE data (eocdPos + 12)).toNat
  let cdOffset := (Binary.readUInt32LE data (eocdPos + 16)).toNat
  return parseCentralDir data cdOffset cdSize

/-- Extract a ZIP archive to an output directory. -/
def extract (inputPath : System.FilePath) (outDir : System.FilePath) : IO Unit := do
  let data ← IO.FS.readBinFile inputPath
  let some eocdPos := findEOCD data
    | throw (IO.userError "zip: cannot find end of central directory")
  let cdSize := (Binary.readUInt32LE data (eocdPos + 12)).toNat
  let cdOffset := (Binary.readUInt32LE data (eocdPos + 16)).toNat
  let entries := parseCentralDir data cdOffset cdSize
  let outDirStr := outDir.toString
  for entry in entries do
    -- Skip directory entries
    if entry.path.endsWith "/" then
      IO.FS.createDirAll (outDir / entry.path)
      continue
    let outPath := outDir / entry.path
    -- Path safety
    let resolved := outPath.toString
    unless resolved.startsWith outDirStr do
      throw (IO.userError s!"zip: path escapes output directory: {entry.path}")
    if let some parent := outPath.parent then
      IO.FS.createDirAll parent
    -- Read local file header to find data start
    let localPos := entry.localOffset.toNat
    let nameLen := (Binary.readUInt16LE data (localPos + 26)).toNat
    let extraLen := (Binary.readUInt16LE data (localPos + 28)).toNat
    let dataStart := localPos + 30 + nameLen + extraLen
    let compData := data.extract dataStart (dataStart + entry.compressedSize.toNat)
    -- Decompress
    let fileData ←
      if entry.method == 0 then
        pure compData  -- stored
      else if entry.method == 8 then
        RawDeflate.decompress compData  -- deflated
      else
        throw (IO.userError s!"zip: unsupported method {entry.method} for {entry.path}")
    -- Verify CRC32
    let actualCrc ← Checksum.crc32 0 fileData
    unless actualCrc == entry.crc32 do
      throw (IO.userError s!"zip: CRC32 mismatch for {entry.path}: expected {entry.crc32}, got {actualCrc}")
    -- Verify size
    unless fileData.size.toUInt32 == entry.uncompressedSize do
      throw (IO.userError s!"zip: size mismatch for {entry.path}")
    IO.FS.writeBinFile outPath fileData

/-- Extract a single file from a ZIP archive by name. -/
def extractFile (inputPath : System.FilePath) (filename : String) : IO ByteArray := do
  let data ← IO.FS.readBinFile inputPath
  let some eocdPos := findEOCD data
    | throw (IO.userError "zip: cannot find end of central directory")
  let cdSize := (Binary.readUInt32LE data (eocdPos + 12)).toNat
  let cdOffset := (Binary.readUInt32LE data (eocdPos + 16)).toNat
  let entries := parseCentralDir data cdOffset cdSize
  let some entry := entries.find? (·.path == filename)
    | throw (IO.userError s!"zip: file not found: {filename}")
  let localPos := entry.localOffset.toNat
  let nameLen := (Binary.readUInt16LE data (localPos + 26)).toNat
  let extraLen := (Binary.readUInt16LE data (localPos + 28)).toNat
  let dataStart := localPos + 30 + nameLen + extraLen
  let compData := data.extract dataStart (dataStart + entry.compressedSize.toNat)
  let fileData ←
    if entry.method == 0 then pure compData
    else if entry.method == 8 then RawDeflate.decompress compData
    else throw (IO.userError s!"zip: unsupported method {entry.method}")
  let actualCrc ← Checksum.crc32 0 fileData
  unless actualCrc == entry.crc32 do
    throw (IO.userError s!"zip: CRC32 mismatch for {filename}")
  return fileData

end Zip
