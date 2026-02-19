import Zip.Binary
import Zip.Checksum
import Zip.Handle
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

/-- Check if an entry needs ZIP64 extra fields. -/
private def needsZip64 (entry : Entry) : Bool :=
  entry.compressedSize >= val32Max.toUInt64 ||
  entry.uncompressedSize >= val32Max.toUInt64 ||
  entry.localOffset >= val32Max.toUInt64

-- DOS date/time encoding (minimal: default to 1980-01-01 00:00:00)
private def defaultDosTime : UInt16 := 0
private def defaultDosDate : UInt16 := 0x0021  -- 1980-01-01

/-- Build a ZIP64 extra field for a local file header (sizes only, no offset). -/
private def writeZip64ExtraLocal (entry : Entry) : ByteArray :=
  Binary.zeros 20
  |> (Binary.writeUInt16LEAt · 0 0x0001)
  |> (Binary.writeUInt16LEAt · 2 16)
  |> (Binary.writeUInt64LEAt · 4 entry.uncompressedSize)
  |> (Binary.writeUInt64LEAt · 12 entry.compressedSize)

/-- Build a ZIP64 extra field for a central directory header (sizes + offset). -/
private def writeZip64ExtraCentral (entry : Entry) : ByteArray :=
  Binary.zeros 28
  |> (Binary.writeUInt16LEAt · 0 0x0001)
  |> (Binary.writeUInt16LEAt · 2 24)
  |> (Binary.writeUInt64LEAt · 4 entry.uncompressedSize)
  |> (Binary.writeUInt64LEAt · 12 entry.compressedSize)
  |> (Binary.writeUInt64LEAt · 20 entry.localOffset)

/-- Write a local file header. Returns the header bytes. -/
private def writeLocalHeader (entry : Entry) : ByteArray := Id.run do
  let nameBytes := entry.path.toUTF8
  let z64 := needsZip64 entry
  let extraField := if z64 then writeZip64ExtraLocal entry else ByteArray.empty
  let totalSize := 30 + nameBytes.size + extraField.size
  let mut buf := Binary.zeros totalSize
  buf := Binary.writeUInt32LEAt buf 0 sigLocal
  buf := Binary.writeUInt16LEAt buf 4 (if z64 then 45 else 20)
  buf := Binary.writeUInt16LEAt buf 6 0x0800  -- flags: bit 11 = UTF-8 names
  buf := Binary.writeUInt16LEAt buf 8 entry.method
  buf := Binary.writeUInt16LEAt buf 10 defaultDosTime
  buf := Binary.writeUInt16LEAt buf 12 defaultDosDate
  buf := Binary.writeUInt32LEAt buf 14 entry.crc32
  if z64 then
    buf := Binary.writeUInt32LEAt buf 18 val32Max
    buf := Binary.writeUInt32LEAt buf 22 val32Max
  else
    buf := Binary.writeUInt32LEAt buf 18 entry.compressedSize.toUInt32
    buf := Binary.writeUInt32LEAt buf 22 entry.uncompressedSize.toUInt32
  buf := Binary.writeUInt16LEAt buf 26 nameBytes.size.toUInt16
  buf := Binary.writeUInt16LEAt buf 28 extraField.size.toUInt16
  buf := Binary.writeField buf 30 nameBytes
  buf := Binary.writeField buf (30 + nameBytes.size) extraField
  return buf

/-- Write a central directory header. Returns the header bytes. -/
private def writeCentralHeader (entry : Entry) : ByteArray := Id.run do
  let nameBytes := entry.path.toUTF8
  let z64 := needsZip64 entry
  let extraField := if z64 then writeZip64ExtraCentral entry else ByteArray.empty
  let totalSize := 46 + nameBytes.size + extraField.size
  let mut buf := Binary.zeros totalSize
  buf := Binary.writeUInt32LEAt buf 0 sigCentral
  buf := Binary.writeUInt16LEAt buf 4 (3 * 256 + (if z64 then 45 else 20))
  buf := Binary.writeUInt16LEAt buf 6 (if z64 then 45 else 20)
  buf := Binary.writeUInt16LEAt buf 8 0x0800  -- flags: bit 11 = UTF-8 names
  buf := Binary.writeUInt16LEAt buf 10 entry.method
  buf := Binary.writeUInt16LEAt buf 12 defaultDosTime
  buf := Binary.writeUInt16LEAt buf 14 defaultDosDate
  buf := Binary.writeUInt32LEAt buf 16 entry.crc32
  if z64 then
    buf := Binary.writeUInt32LEAt buf 20 val32Max
    buf := Binary.writeUInt32LEAt buf 24 val32Max
  else
    buf := Binary.writeUInt32LEAt buf 20 entry.compressedSize.toUInt32
    buf := Binary.writeUInt32LEAt buf 24 entry.uncompressedSize.toUInt32
  buf := Binary.writeUInt16LEAt buf 28 nameBytes.size.toUInt16
  buf := Binary.writeUInt16LEAt buf 30 extraField.size.toUInt16
  -- comment length (32), disk number start (34), internal attrs (36): all 0 from zeros
  -- external attrs (38): 0 from zeros
  if z64 then
    buf := Binary.writeUInt32LEAt buf 42 val32Max
  else
    buf := Binary.writeUInt32LEAt buf 42 entry.localOffset.toUInt32
  buf := Binary.writeField buf 46 nameBytes
  buf := Binary.writeField buf (46 + nameBytes.size) extraField
  return buf

/-- Write end of central directory records. Includes ZIP64 EOCD + locator when needed. -/
private def writeEndRecords (numEntries : Nat) (cdSize cdOffset : UInt64) : ByteArray := Id.run do
  let need64 := numEntries > 65535 || cdSize >= val32Max.toUInt64 || cdOffset >= val32Max.toUInt64
  -- ZIP64 EOCD (56) + ZIP64 Locator (20) + Standard EOCD (22)
  let z64Size := if need64 then 76 else 0
  let totalSize := z64Size + 22
  let mut buf := Binary.zeros totalSize
  if need64 then
    let eocd64Offset := cdOffset + cdSize
    -- ZIP64 End of Central Directory Record (56 bytes)
    buf := Binary.writeUInt32LEAt buf 0 sigEOCD64
    buf := Binary.writeUInt64LEAt buf 4 44  -- size of remaining EOCD64
    buf := Binary.writeUInt16LEAt buf 12 (3 * 256 + 45)  -- version made by
    buf := Binary.writeUInt16LEAt buf 14 45  -- version needed
    -- disk number (16) and disk with CD (20): 0 from zeros
    buf := Binary.writeUInt64LEAt buf 24 numEntries.toUInt64  -- entries on disk
    buf := Binary.writeUInt64LEAt buf 32 numEntries.toUInt64  -- total entries
    buf := Binary.writeUInt64LEAt buf 40 cdSize
    buf := Binary.writeUInt64LEAt buf 48 cdOffset
    -- ZIP64 End of Central Directory Locator (20 bytes)
    buf := Binary.writeUInt32LEAt buf 56 sigLocator64
    -- disk with EOCD64 (60): 0 from zeros
    buf := Binary.writeUInt64LEAt buf 64 eocd64Offset
    buf := Binary.writeUInt32LEAt buf 72 1  -- total disks
  -- Standard EOCD (22 bytes)
  let eocdOff := z64Size
  buf := Binary.writeUInt32LEAt buf eocdOff sigEOCD
  -- disk number (eocdOff+4), disk with CD (eocdOff+6): 0 from zeros
  let numEntries16 := if numEntries > 65535 then val16Max else numEntries.toUInt16
  buf := Binary.writeUInt16LEAt buf (eocdOff + 8) numEntries16
  buf := Binary.writeUInt16LEAt buf (eocdOff + 10) numEntries16
  let cdSize32 := if cdSize >= val32Max.toUInt64 then val32Max else cdSize.toUInt32
  buf := Binary.writeUInt32LEAt buf (eocdOff + 12) cdSize32
  let cdOffset32 := if cdOffset >= val32Max.toUInt64 then val32Max else cdOffset.toUInt32
  buf := Binary.writeUInt32LEAt buf (eocdOff + 16) cdOffset32
  -- comment length (eocdOff + 20): 0 from zeros
  return buf

/-- Create a ZIP archive from (archivePath, diskPath) pairs.
    Streams local file entries directly to disk to avoid O(archive_size) memory. -/
def create (outputPath : System.FilePath)
    (files : Array (String × System.FilePath)) : IO Unit := do
  IO.FS.withFile outputPath .write fun outH => do
    let outStream := IO.FS.Stream.ofHandle outH
    let mut entries : Array Entry := #[]
    let mut offset : UInt64 := 0
    for (archiveName, diskPath) in files do
      let fileData ← IO.FS.readBinFile diskPath
      let crc := Checksum.crc32 0 fileData
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
      outStream.write localHdr
      outStream.write compData
      offset := offset + localHdr.size.toUInt64 + compData.size.toUInt64
    -- Stream each central directory header directly (avoids quadratic concatenation)
    let cdOffset := offset
    let mut cdSize : Nat := 0
    for entry in entries do
      let hdr := writeCentralHeader entry
      outStream.write hdr
      cdSize := cdSize + hdr.size
    let endRecs := writeEndRecords entries.size cdSize.toUInt64 cdOffset
    outStream.write endRecs

/-- Create a ZIP archive from all files under a directory. -/
partial def createFromDir (outputPath : System.FilePath) (dir : System.FilePath) : IO Unit := do
  let allFiles ← dir.walkDir
  let sorted := allFiles.qsort (·.toString < ·.toString)
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

/-- Find the EOCD record in a (possibly tail-) buffer.
    `baseOffset` is the file-absolute byte offset where `data` starts (0 for full file).
    Returns `(eocdPos, cdOffset, cdSize)` where cdOffset/cdSize are file-absolute. -/
private def findEndOfCentralDir (data : ByteArray) (baseOffset : Nat := 0)
    : Option (Nat × Nat × Nat) := Id.run do
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
  -- Read standard EOCD values (file-absolute)
  let mut cdSize := (Binary.readUInt32LE data (pos + 12)).toNat
  let mut cdOffset := (Binary.readUInt32LE data (pos + 16)).toNat
  -- Check for ZIP64 EOCD Locator (20 bytes before standard EOCD)
  if pos >= 20 then
    if Binary.readUInt32LE data (pos - 20) == sigLocator64 then
      let eocd64Offset := (Binary.readUInt64LE data (pos - 12)).toNat
      -- Convert file-absolute offset to buffer-relative
      if eocd64Offset >= baseOffset then
        let bufPos := eocd64Offset - baseOffset
        if bufPos + 56 <= data.size then
          if Binary.readUInt32LE data bufPos == sigEOCD64 then
            cdSize := (Binary.readUInt64LE data (bufPos + 40)).toNat
            cdOffset := (Binary.readUInt64LE data (bufPos + 48)).toNat
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
    -- Guard against malformed extra field length extending past buffer
    if epos + 4 + dataSize > extraData.size then break
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
    let flags := Binary.readUInt16LE data (pos + 8)
    let method := Binary.readUInt16LE data (pos + 10)
    let crc := Binary.readUInt32LE data (pos + 16)
    let stdCompSize := Binary.readUInt32LE data (pos + 20)
    let stdUncompSize := Binary.readUInt32LE data (pos + 24)
    let nameLen := (Binary.readUInt16LE data (pos + 28)).toNat
    let extraLen := (Binary.readUInt16LE data (pos + 30)).toNat
    let commentLen := (Binary.readUInt16LE data (pos + 32)).toNat
    let entryEnd := pos + 46 + nameLen + extraLen + commentLen
    if entryEnd > cdEnd then
      throw (IO.userError "zip: central directory entry extends past end of central directory")
    let stdOffset := Binary.readUInt32LE data (pos + 42)
    let nameBytes := data.extract (pos + 46) (pos + 46 + nameLen)
    let name ←
      if flags &&& 0x0800 != 0 then
        -- UTF-8 flag set: validate UTF-8 strictly
        match String.fromUTF8? nameBytes with
        | some s => pure s
        | none => throw (IO.userError "zip: invalid UTF-8 in entry name (UTF-8 flag set)")
      else
        -- No UTF-8 flag: try UTF-8 first, fall back to Latin-1
        pure (match String.fromUTF8? nameBytes with
          | some s => s
          | none => Binary.fromLatin1 nameBytes)
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

/-- Read exactly `n` bytes from a handle, throwing on short read.
    Loops to handle short reads from pipes/network streams. -/
private partial def readExact (h : IO.FS.Handle) (n : Nat) (what : String) : IO ByteArray := do
  unless n.toUSize.toNat == n do
    throw (IO.userError s!"zip: {what} size {n} exceeds addressable range")
  let mut buf := ByteArray.empty
  while buf.size < n do
    let remaining := n - buf.size
    let chunk ← h.read remaining.toUSize
    if chunk.isEmpty then
      throw (IO.userError s!"zip: short read for {what}: expected {n}, got {buf.size}")
    buf := buf ++ chunk
  return buf

/-- Read exactly `n` bytes from a stream, throwing on premature EOF.
    Loops to handle short reads from pipes/network streams. -/
partial def readExactStream (s : IO.FS.Stream) (n : Nat) (what : String) : IO ByteArray := do
  unless n.toUSize.toNat == n do
    throw (IO.userError s!"zip: {what} size {n} exceeds addressable range")
  let mut buf := ByteArray.empty
  while buf.size < n do
    let remaining := n - buf.size
    let chunk ← s.read remaining.toUSize
    if chunk.isEmpty then
      throw (IO.userError s!"zip: short read for {what}: expected {n}, got {buf.size}")
    buf := buf ++ chunk
  return buf

/-- Read entries from a file handle by seeking to the tail, EOCD, and central directory.
    Memory usage: O(65KB + central directory size). -/
private def listFromHandle (h : IO.FS.Handle) (maxCentralDirSize : Nat := 67108864) : IO (Array Entry) := do
  let fileSize := (← Handle.fileSize h).toNat
  -- Read tail (last 65558 bytes) to find EOCD
  -- 65558 = 22 (min EOCD) + 65535 (max comment) + 1
  let tailSize := min fileSize 65558
  let tailStart := fileSize - tailSize
  Handle.seek h tailStart.toUInt64
  let tail ← readExact h tailSize "EOCD tail"
  let some (_, cdOffset, cdSize) := findEndOfCentralDir tail tailStart
    | throw (IO.userError "zip: cannot find end of central directory")
  unless cdOffset + cdSize <= fileSize do
    throw (IO.userError "zip: central directory extends beyond file")
  if maxCentralDirSize > 0 && cdSize > maxCentralDirSize then
    throw (IO.userError s!"zip: central directory too large ({cdSize} bytes, limit {maxCentralDirSize})")
  -- Read just the central directory
  Handle.seek h cdOffset.toUInt64
  let cdBuf ← readExact h cdSize "central directory"
  parseCentralDir cdBuf 0 cdSize

/-- Read an entry's decompressed data from a file handle by seeking to its local header.
    `maxEntrySize` limits decompressed entry size (0 = no limit). -/
private def readEntryData (h : IO.FS.Handle) (entry : Entry) (label : String)
    (maxEntrySize : UInt64 := 0) : IO ByteArray := do
  if maxEntrySize > 0 && entry.uncompressedSize > maxEntrySize then
    throw (IO.userError s!"zip: entry '{label}' uncompressed size ({entry.uncompressedSize}) exceeds limit ({maxEntrySize})")
  Handle.seek h entry.localOffset
  let localHdr ← readExact h 30 s!"local header for {label}"
  unless Binary.readUInt32LE localHdr 0 == sigLocal do
    throw (IO.userError s!"zip: bad local header signature for {label}")
  let nameLen := (Binary.readUInt16LE localHdr 26).toNat
  let extraLen := (Binary.readUInt16LE localHdr 28).toNat
  let _ ← readExact h (nameLen + extraLen) s!"local name+extra for {label}"
  let compData ← readExact h entry.compressedSize.toNat s!"compressed data for {label}"
  let fileData ←
    if entry.method == 0 then pure compData
    else if entry.method == 8 then RawDeflate.decompress compData maxEntrySize
    else throw (IO.userError s!"zip: unsupported method {entry.method} for {label}")
  let actualCrc := Checksum.crc32 0 fileData
  unless actualCrc == entry.crc32 do
    throw (IO.userError s!"zip: CRC32 mismatch for {label}: expected {entry.crc32}, got {actualCrc}")
  unless fileData.size.toUInt64 == entry.uncompressedSize do
    throw (IO.userError s!"zip: size mismatch for {label}")
  return fileData

/-- List entries in a ZIP archive. Memory: O(65KB + central directory metadata).
    `maxCentralDirSize` limits the central directory allocation (default 64MB, 0 = no limit). -/
def list (inputPath : System.FilePath) (maxCentralDirSize : Nat := 67108864) : IO (Array Entry) :=
  IO.FS.withFile inputPath .read (listFromHandle · maxCentralDirSize)

/-- Extract a ZIP archive to an output directory.
    Memory: O(65KB + central directory + largest single file). -/
def extract (inputPath : System.FilePath) (outDir : System.FilePath)
    (maxCentralDirSize : Nat := 67108864) (maxEntrySize : UInt64 := 0) : IO Unit := do
  IO.FS.withFile inputPath .read fun h => do
    let entries ← listFromHandle h maxCentralDirSize
    for entry in entries do
      -- Strip trailing slash for path safety check (directories end with "/")
      let checkPath := if entry.path.endsWith "/" then entry.path.dropEnd 1 |>.toString else entry.path
      if entry.path.endsWith "/" then
        unless Binary.isPathSafe checkPath do
          throw (IO.userError s!"zip: unsafe path: {entry.path}")
        IO.FS.createDirAll (outDir / entry.path)
        continue
      unless Binary.isPathSafe checkPath do
        throw (IO.userError s!"zip: unsafe path: {entry.path}")
      let outPath := outDir / entry.path
      if let some parent := outPath.parent then
        IO.FS.createDirAll parent
      let fileData ← readEntryData h entry entry.path maxEntrySize
      IO.FS.writeBinFile outPath fileData

/-- Extract a single file from a ZIP archive by name.
    Memory: O(65KB + central directory + target file). -/
def extractFile (inputPath : System.FilePath) (filename : String)
    (maxCentralDirSize : Nat := 67108864) (maxEntrySize : UInt64 := 0) : IO ByteArray := do
  IO.FS.withFile inputPath .read fun h => do
    let entries ← listFromHandle h maxCentralDirSize
    let some entry := entries.find? (·.path == filename)
      | throw (IO.userError s!"zip: file not found: {filename}")
    readEntryData h entry filename maxEntrySize

end Archive
