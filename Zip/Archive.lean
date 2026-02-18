import Zip.Binary
import Zip.Checksum
import Zip.RawDeflate

namespace Archive

-- ZIP signatures
private def sigLocal    : UInt32 := 0x04034b50
private def sigCentral  : UInt32 := 0x02014b50
private def sigEOCD     : UInt32 := 0x06054b50
private def sigEOCD64   : UInt32 := 0x06064b50
private def sigLocator64 : UInt32 := 0x07064b50

-- Sentinel values indicating ZIP64 is needed
private def val32Max : UInt32 := 0xFFFFFFFF
private def val16Max : UInt16 := 0xFFFF

/-- ZIP entry metadata. Sizes and offsets are 64-bit to support ZIP64. -/
structure Entry where
  path             : String
  compressedSize   : UInt64 := 0
  uncompressedSize : UInt64 := 0
  crc32            : UInt32 := 0
  method           : UInt16 := 0  -- 0 = stored, 8 = deflated
  localOffset      : UInt64 := 0
  deriving Repr, Inhabited

/-- Check if a path is safe for extraction (no `..` segments, not absolute). -/
private def isPathSafe (path : String) : Bool := Id.run do
  if path.startsWith "/" then return false
  let components := path.splitOn "/"
  for c in components do
    if c == ".." then return false
  return true

/-- Check if an entry needs ZIP64 extra fields. -/
private def needsZip64 (entry : Entry) : Bool :=
  entry.compressedSize >= val32Max.toUInt64 ||
  entry.uncompressedSize >= val32Max.toUInt64 ||
  entry.localOffset >= val32Max.toUInt64

-- DOS date/time encoding (minimal: default to 1980-01-01 00:00:00)
private def defaultDosTime : UInt16 := 0
private def defaultDosDate : UInt16 := 0x0021  -- 1980-01-01

/-- Build a ZIP64 extra field for a local file header (sizes only, no offset). -/
private def writeZip64ExtraLocal (entry : Entry) : ByteArray := Id.run do
  let mut buf := ByteArray.empty
  buf := buf ++ Binary.writeUInt16LE 0x0001
  buf := buf ++ Binary.writeUInt16LE 16  -- 2 × 8 bytes
  buf := buf ++ Binary.writeUInt64LE entry.uncompressedSize
  buf := buf ++ Binary.writeUInt64LE entry.compressedSize
  return buf

/-- Build a ZIP64 extra field for a central directory header (sizes + offset). -/
private def writeZip64ExtraCentral (entry : Entry) : ByteArray := Id.run do
  let mut buf := ByteArray.empty
  buf := buf ++ Binary.writeUInt16LE 0x0001
  buf := buf ++ Binary.writeUInt16LE 24  -- 3 × 8 bytes
  buf := buf ++ Binary.writeUInt64LE entry.uncompressedSize
  buf := buf ++ Binary.writeUInt64LE entry.compressedSize
  buf := buf ++ Binary.writeUInt64LE entry.localOffset
  return buf

/-- Write a local file header. Returns the header bytes. -/
private def writeLocalHeader (entry : Entry) : ByteArray := Id.run do
  let nameBytes := entry.path.toUTF8
  let z64 := needsZip64 entry
  let extraField := if z64 then writeZip64ExtraLocal entry else ByteArray.empty
  let mut buf := ByteArray.empty
  buf := buf ++ Binary.writeUInt32LE sigLocal
  -- Version needed: 4.5 (45) for ZIP64, 2.0 (20) otherwise
  buf := buf ++ Binary.writeUInt16LE (if z64 then 45 else 20)
  buf := buf ++ Binary.writeUInt16LE 0  -- flags
  buf := buf ++ Binary.writeUInt16LE entry.method
  buf := buf ++ Binary.writeUInt16LE defaultDosTime
  buf := buf ++ Binary.writeUInt16LE defaultDosDate
  buf := buf ++ Binary.writeUInt32LE entry.crc32
  -- Sizes: use 0xFFFFFFFF sentinel when ZIP64
  if z64 then
    buf := buf ++ Binary.writeUInt32LE val32Max
    buf := buf ++ Binary.writeUInt32LE val32Max
  else
    buf := buf ++ Binary.writeUInt32LE entry.compressedSize.toUInt32
    buf := buf ++ Binary.writeUInt32LE entry.uncompressedSize.toUInt32
  buf := buf ++ Binary.writeUInt16LE nameBytes.size.toUInt16
  buf := buf ++ Binary.writeUInt16LE extraField.size.toUInt16
  buf := buf ++ nameBytes
  buf := buf ++ extraField
  return buf

/-- Write a central directory header. Returns the header bytes. -/
private def writeCentralHeader (entry : Entry) : ByteArray := Id.run do
  let nameBytes := entry.path.toUTF8
  let z64 := needsZip64 entry
  let extraField := if z64 then writeZip64ExtraCentral entry else ByteArray.empty
  let mut buf := ByteArray.empty
  buf := buf ++ Binary.writeUInt32LE sigCentral
  -- Version made by: 4.5 (45) for ZIP64, Unix (3)
  buf := buf ++ Binary.writeUInt16LE (3 * 256 + (if z64 then 45 else 20))
  -- Version needed
  buf := buf ++ Binary.writeUInt16LE (if z64 then 45 else 20)
  buf := buf ++ Binary.writeUInt16LE 0  -- flags
  buf := buf ++ Binary.writeUInt16LE entry.method
  buf := buf ++ Binary.writeUInt16LE defaultDosTime
  buf := buf ++ Binary.writeUInt16LE defaultDosDate
  buf := buf ++ Binary.writeUInt32LE entry.crc32
  if z64 then
    buf := buf ++ Binary.writeUInt32LE val32Max
    buf := buf ++ Binary.writeUInt32LE val32Max
  else
    buf := buf ++ Binary.writeUInt32LE entry.compressedSize.toUInt32
    buf := buf ++ Binary.writeUInt32LE entry.uncompressedSize.toUInt32
  buf := buf ++ Binary.writeUInt16LE nameBytes.size.toUInt16
  buf := buf ++ Binary.writeUInt16LE extraField.size.toUInt16
  buf := buf ++ Binary.writeUInt16LE 0  -- comment length
  buf := buf ++ Binary.writeUInt16LE 0  -- disk number start
  buf := buf ++ Binary.writeUInt16LE 0  -- internal attrs
  buf := buf ++ Binary.writeUInt32LE 0  -- external attrs
  if z64 then
    buf := buf ++ Binary.writeUInt32LE val32Max
  else
    buf := buf ++ Binary.writeUInt32LE entry.localOffset.toUInt32
  buf := buf ++ nameBytes
  buf := buf ++ extraField
  return buf

/-- Write end of central directory records. Includes ZIP64 EOCD + locator when needed. -/
private def writeEndRecords (numEntries : Nat) (cdSize cdOffset : UInt64) : ByteArray := Id.run do
  let need64 := numEntries > 65535 || cdSize >= val32Max.toUInt64 || cdOffset >= val32Max.toUInt64
  let mut buf := ByteArray.empty
  if need64 then
    -- ZIP64 End of Central Directory Record
    let eocd64Offset := cdOffset + cdSize  -- offset of this record
    buf := buf ++ Binary.writeUInt32LE sigEOCD64
    buf := buf ++ Binary.writeUInt64LE 44  -- size of remaining EOCD64 (56 - 12)
    buf := buf ++ Binary.writeUInt16LE (3 * 256 + 45)  -- version made by
    buf := buf ++ Binary.writeUInt16LE 45  -- version needed
    buf := buf ++ Binary.writeUInt32LE 0  -- disk number
    buf := buf ++ Binary.writeUInt32LE 0  -- disk with CD
    buf := buf ++ Binary.writeUInt64LE numEntries.toUInt64  -- entries on disk
    buf := buf ++ Binary.writeUInt64LE numEntries.toUInt64  -- total entries
    buf := buf ++ Binary.writeUInt64LE cdSize  -- CD size
    buf := buf ++ Binary.writeUInt64LE cdOffset  -- CD offset
    -- ZIP64 End of Central Directory Locator
    buf := buf ++ Binary.writeUInt32LE sigLocator64
    buf := buf ++ Binary.writeUInt32LE 0  -- disk with EOCD64
    buf := buf ++ Binary.writeUInt64LE eocd64Offset  -- offset of EOCD64
    buf := buf ++ Binary.writeUInt32LE 1  -- total disks
  -- Standard EOCD (always written)
  buf := buf ++ Binary.writeUInt32LE sigEOCD
  buf := buf ++ Binary.writeUInt16LE 0  -- disk number
  buf := buf ++ Binary.writeUInt16LE 0  -- disk with CD
  let numEntries16 := if numEntries > 65535 then val16Max else numEntries.toUInt16
  buf := buf ++ Binary.writeUInt16LE numEntries16
  buf := buf ++ Binary.writeUInt16LE numEntries16
  let cdSize32 := if cdSize >= val32Max.toUInt64 then val32Max else cdSize.toUInt32
  buf := buf ++ Binary.writeUInt32LE cdSize32
  let cdOffset32 := if cdOffset >= val32Max.toUInt64 then val32Max else cdOffset.toUInt32
  buf := buf ++ Binary.writeUInt32LE cdOffset32
  buf := buf ++ Binary.writeUInt16LE 0  -- comment length
  return buf

/-- Create a ZIP archive from (archivePath, diskPath) pairs. -/
def create (outputPath : System.FilePath)
    (files : Array (String × System.FilePath)) : IO Unit := do
  let mut entries : Array Entry := #[]
  let mut offset : UInt64 := 0
  let mut body := ByteArray.empty
  for (archiveName, diskPath) in files do
    let fileData ← IO.FS.readBinFile diskPath
    let crc ← Checksum.crc32 0 fileData
    let deflated ← RawDeflate.compress fileData
    let useDeflate := deflated.size < fileData.size
    let method : UInt16 := if useDeflate then 8 else 0
    let compData := if useDeflate then deflated else fileData
    let entry : Entry := {
      path := archiveName
      compressedSize := compData.size.toUInt64
      uncompressedSize := fileData.size.toUInt64
      crc32 := crc
      method := method
      localOffset := offset
    }
    entries := entries.push entry
    let localHdr := writeLocalHeader entry
    body := body ++ localHdr ++ compData
    offset := offset + localHdr.size.toUInt64 + compData.size.toUInt64
  let cdOffset := offset
  let mut cd := ByteArray.empty
  for entry in entries do
    cd := cd ++ writeCentralHeader entry
  let endRecs := writeEndRecords entries.size cd.size.toUInt64 cdOffset
  IO.FS.writeBinFile outputPath (body ++ cd ++ endRecs)

/-- Create a ZIP archive from all files under a directory. -/
partial def createFromDir (outputPath : System.FilePath) (dir : System.FilePath) : IO Unit := do
  let allFiles ← dir.walkDir
  let sorted := allFiles.insertionSort (·.toString < ·.toString)
  let dirStr := dir.toString
  let dirPfx := if dirStr.endsWith "/" then dirStr else dirStr ++ "/"
  let mut pairs : Array (String × System.FilePath) := #[]
  for file in sorted do
    let fmeta ← file.metadata
    if fmeta.type == .dir then continue
    let fileStr := file.toString
    if fileStr == dirStr then continue
    let relPath :=
      if fileStr.startsWith dirPfx then
        (fileStr.drop dirPfx.length).toString
      else fileStr
    if relPath.isEmpty then continue
    pairs := pairs.push (relPath, file)
  create outputPath pairs

/-- Find the EOCD record in a ZIP file. Returns (eocdPos, cdOffset, cdSize, numEntries).
    Handles both standard and ZIP64 EOCD. -/
private def findEndOfCentralDir (data : ByteArray) : Option (Nat × Nat × Nat) := Id.run do
  -- Find standard EOCD
  if data.size < 22 then return none
  let mut eocdPos : Option Nat := none
  let mut i := data.size - 22
  let minPos := if data.size > 65557 then data.size - 65557 else 0
  while i >= minPos do
    if Binary.readUInt32LE data i == sigEOCD then
      eocdPos := some i
      break
    if i == 0 then break
    i := i - 1
  let some pos := eocdPos | return none
  -- Read standard EOCD values
  let mut cdSize := (Binary.readUInt32LE data (pos + 12)).toNat
  let mut cdOffset := (Binary.readUInt32LE data (pos + 16)).toNat
  -- Check for ZIP64 EOCD Locator (20 bytes before standard EOCD)
  if pos >= 20 then
    if Binary.readUInt32LE data (pos - 20) == sigLocator64 then
      let eocd64Offset := (Binary.readUInt64LE data (pos - 12)).toNat
      -- Read ZIP64 EOCD
      if eocd64Offset + 56 <= data.size then
        if Binary.readUInt32LE data eocd64Offset == sigEOCD64 then
          cdSize := (Binary.readUInt64LE data (eocd64Offset + 40)).toNat
          cdOffset := (Binary.readUInt64LE data (eocd64Offset + 48)).toNat
  return some (pos, cdOffset, cdSize)

/-- Parse a ZIP64 extra field from extra data, returning (uncompressedSize, compressedSize, offset).
    Only reads fields whose standard values are 0xFFFFFFFF. Returns `none` if a required field
    is missing from the ZIP64 extra data. -/
private def parseZip64Extra (extraData : ByteArray) (stdUncomp stdComp stdOffset : UInt32)
    : Option (UInt64 × UInt64 × UInt64) := Id.run do
  let mut uncompSize := stdUncomp.toUInt64
  let mut compSize := stdComp.toUInt64
  let mut localOff := stdOffset.toUInt64
  -- Search for ZIP64 extra field (ID 0x0001)
  let mut epos := 0
  let mut found := false
  while epos + 4 <= extraData.size do
    let headerId := Binary.readUInt16LE extraData epos
    let dataSize := (Binary.readUInt16LE extraData (epos + 2)).toNat
    if headerId == 0x0001 then
      found := true
      let mut fpos := epos + 4
      let fieldEnd := epos + 4 + dataSize
      if stdUncomp == val32Max then
        if fpos + 8 > fieldEnd then return none
        uncompSize := Binary.readUInt64LE extraData fpos
        fpos := fpos + 8
      if stdComp == val32Max then
        if fpos + 8 > fieldEnd then return none
        compSize := Binary.readUInt64LE extraData fpos
        fpos := fpos + 8
      if stdOffset == val32Max then
        if fpos + 8 > fieldEnd then return none
        localOff := Binary.readUInt64LE extraData fpos
      break
    epos := epos + 4 + dataSize
  -- If any field needs ZIP64 but the extra field wasn't found, fail
  if !found && (stdUncomp == val32Max || stdComp == val32Max || stdOffset == val32Max) then
    return none
  return some (uncompSize, compSize, localOff)

/-- Parse central directory entries from a ZIP file. -/
private def parseCentralDir (data : ByteArray) (cdOffset cdSize : Nat) : IO (Array Entry) := do
  let mut entries : Array Entry := #[]
  let mut pos := cdOffset
  let cdEnd := cdOffset + cdSize
  while pos + 46 <= cdEnd do
    let sig := Binary.readUInt32LE data pos
    if sig != sigCentral then break
    let method := Binary.readUInt16LE data (pos + 10)
    let crc := Binary.readUInt32LE data (pos + 16)
    let stdCompSize := Binary.readUInt32LE data (pos + 20)
    let stdUncompSize := Binary.readUInt32LE data (pos + 24)
    let nameLen := (Binary.readUInt16LE data (pos + 28)).toNat
    let extraLen := (Binary.readUInt16LE data (pos + 30)).toNat
    let commentLen := (Binary.readUInt16LE data (pos + 32)).toNat
    let stdOffset := Binary.readUInt32LE data (pos + 42)
    let nameBytes := data.extract (pos + 46) (pos + 46 + nameLen)
    let name := String.fromUTF8! nameBytes
    -- Parse ZIP64 extra field if any standard field is 0xFFFFFFFF
    let extraData := data.extract (pos + 46 + nameLen) (pos + 46 + nameLen + extraLen)
    let (uncompSize, compSize, localOff) ←
      if stdCompSize == val32Max || stdUncompSize == val32Max || stdOffset == val32Max then
        match parseZip64Extra extraData stdUncompSize stdCompSize stdOffset with
        | some v => pure v
        | none => throw (IO.userError s!"zip: truncated ZIP64 extra field for {name}")
      else
        pure (stdUncompSize.toUInt64, stdCompSize.toUInt64, stdOffset.toUInt64)
    entries := entries.push {
      path := name
      compressedSize := compSize
      uncompressedSize := uncompSize
      crc32 := crc
      method := method
      localOffset := localOff
    }
    pos := pos + 46 + nameLen + extraLen + commentLen
  return entries

/-- List entries in a ZIP archive. -/
def list (inputPath : System.FilePath) : IO (Array Entry) := do
  let data ← IO.FS.readBinFile inputPath
  let some (_, cdOffset, cdSize) := findEndOfCentralDir data
    | throw (IO.userError "zip: cannot find end of central directory")
  unless cdOffset + cdSize <= data.size do
    throw (IO.userError "zip: central directory extends beyond file")
  parseCentralDir data cdOffset cdSize

/-- Extract a ZIP archive to an output directory. -/
def extract (inputPath : System.FilePath) (outDir : System.FilePath) : IO Unit := do
  let data ← IO.FS.readBinFile inputPath
  let some (_, cdOffset, cdSize) := findEndOfCentralDir data
    | throw (IO.userError "zip: cannot find end of central directory")
  unless cdOffset + cdSize <= data.size do
    throw (IO.userError "zip: central directory extends beyond file")
  let entries ← parseCentralDir data cdOffset cdSize
  for entry in entries do
    if entry.path.endsWith "/" then
      if isPathSafe entry.path then
        IO.FS.createDirAll (outDir / entry.path)
      continue
    unless isPathSafe entry.path do
      throw (IO.userError s!"zip: unsafe path: {entry.path}")
    let outPath := outDir / entry.path
    if let some parent := outPath.parent then
      IO.FS.createDirAll parent
    let localPos := entry.localOffset.toNat
    unless localPos + 30 <= data.size do
      throw (IO.userError s!"zip: local header out of bounds for {entry.path}")
    let nameLen := (Binary.readUInt16LE data (localPos + 26)).toNat
    let extraLen := (Binary.readUInt16LE data (localPos + 28)).toNat
    let dataStart := localPos + 30 + nameLen + extraLen
    unless dataStart + entry.compressedSize.toNat <= data.size do
      throw (IO.userError s!"zip: file data out of bounds for {entry.path}")
    let compData := data.extract dataStart (dataStart + entry.compressedSize.toNat)
    let fileData ←
      if entry.method == 0 then pure compData
      else if entry.method == 8 then RawDeflate.decompress compData
      else throw (IO.userError s!"zip: unsupported method {entry.method} for {entry.path}")
    let actualCrc ← Checksum.crc32 0 fileData
    unless actualCrc == entry.crc32 do
      throw (IO.userError s!"zip: CRC32 mismatch for {entry.path}: expected {entry.crc32}, got {actualCrc}")
    unless fileData.size.toUInt64 == entry.uncompressedSize do
      throw (IO.userError s!"zip: size mismatch for {entry.path}")
    IO.FS.writeBinFile outPath fileData

/-- Extract a single file from a ZIP archive by name. -/
def extractFile (inputPath : System.FilePath) (filename : String) : IO ByteArray := do
  let data ← IO.FS.readBinFile inputPath
  let some (_, cdOffset, cdSize) := findEndOfCentralDir data
    | throw (IO.userError "zip: cannot find end of central directory")
  unless cdOffset + cdSize <= data.size do
    throw (IO.userError "zip: central directory extends beyond file")
  let entries ← parseCentralDir data cdOffset cdSize
  let some entry := entries.find? (·.path == filename)
    | throw (IO.userError s!"zip: file not found: {filename}")
  let localPos := entry.localOffset.toNat
  unless localPos + 30 <= data.size do
    throw (IO.userError s!"zip: local header out of bounds for {filename}")
  let nameLen := (Binary.readUInt16LE data (localPos + 26)).toNat
  let extraLen := (Binary.readUInt16LE data (localPos + 28)).toNat
  let dataStart := localPos + 30 + nameLen + extraLen
  unless dataStart + entry.compressedSize.toNat <= data.size do
    throw (IO.userError s!"zip: file data out of bounds for {filename}")
  let compData := data.extract dataStart (dataStart + entry.compressedSize.toNat)
  let fileData ←
    if entry.method == 0 then pure compData
    else if entry.method == 8 then RawDeflate.decompress compData
    else throw (IO.userError s!"zip: unsupported method {entry.method}")
  let actualCrc ← Checksum.crc32 0 fileData
  unless actualCrc == entry.crc32 do
    throw (IO.userError s!"zip: CRC32 mismatch for {filename}")
  return fileData

end Archive
