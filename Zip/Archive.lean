import ZipCommon.Binary
import Zip.Checksum
import ZipCommon.Handle
import Zip.RawDeflate
import Zip.Native.Inflate
import Zip.Native.Crc32

/-! ZIP archive construction and extraction: entry metadata, local/central headers,
    ZIP64 support, and streaming archive creation/extraction. -/

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
private def dataDescriptorBitMask : UInt16 := 0xFFF7  -- CD/LH flag comparison: all bits except bit 3 (data-descriptor presence is a per-LH concern)

/-- ZIP entry metadata. Sizes and offsets are 64-bit to support ZIP64. -/
structure Entry where
  path             : String
  compressedSize   : UInt64 := 0
  uncompressedSize : UInt64 := 0
  crc32            : UInt32 := 0
  method           : UInt16 := 0  -- 0 = stored, 8 = deflated
  localOffset      : UInt64 := 0
  -- Central-directory general-purpose bit flag word, carried through so
  -- `readEntryData` can enforce CD/LH flags consistency (bit 11 UTF-8 name,
  -- etc.). Writers ignore this field and emit a fixed `0x0800` flag word.
  flags            : UInt16 := 0
  -- CD-side `versionNeededToExtract` field (APPNOTE §4.4.3.2),
  -- preserved for CD-vs-LH consistency checking.  Writers ignore this
  -- field and emit a fixed value (`20` for non-ZIP64, `45` for ZIP64);
  -- the check in `readEntryData` only rejects LH claiming a higher
  -- version than CD.
  versionNeeded    : UInt16 := 0
  -- CD-side DOS-encoded last-modified time (APPNOTE §4.4.6), preserved
  -- for CD-vs-LH consistency checking.  Writers ignore this field and
  -- emit `defaultDosTime`.  Default `0` preserves byte-identity for
  -- field-name-syntax constructions (tests and direct callers).
  lastModTime      : UInt16 := 0
  -- CD-side DOS-encoded last-modified date (APPNOTE §4.4.6), preserved
  -- for CD-vs-LH consistency checking.  Writers ignore this field and
  -- emit `defaultDosDate`.  Default `0` preserves byte-identity for
  -- field-name-syntax constructions (tests and direct callers).
  lastModDate      : UInt16 := 0
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
    Returns
    `(eocdPos, cdOffset, cdSize, totalEntries, numberOfThisDisk, diskWhereCDStarts,
     numEntriesThisDisk)` where cdOffset/cdSize are file-absolute, totalEntries is
    the EOCD-advertised CD entry count, the two disk-number fields carry the
    single-disk invariant, and `numEntriesThisDisk` is the sibling entry-count
    field. All fields are read from the standard EOCD and overridden by the
    ZIP64 EOCD64 block when present. lean-zip writes single-disk archives only,
    so `numEntriesThisDisk` is expected to equal `totalEntries`; the pair is
    threaded through for a consistency check in `parseCentralDir`.

    When the ZIP64 EOCD Locator + EOCD64 pair is found and the ZIP64 record
    overrides one of the standard-EOCD fields
    (cdSize/cdOffset/totalEntries/numberOfThisDisk/diskWhereCDStarts/
    numEntriesThisDisk), this raises an `IO.userError` containing
    `"EOCD ZIP64-override mismatch"` unless the standard-EOCD field carries
    the APPNOTE §4.3.16 sentinel — 0xFFFFFFFF for 4-byte fields, 0xFFFF for
    2-byte fields — or numerically matches the ZIP64 override (real-world
    producers such as Go's `archive/zip` emit ZIP64 with real zeros in the
    standard-EOCD disk-number slots, not sentinels). A non-sentinel standard
    value combined with a numerically differing ZIP64 value is a
    parser-differential smuggling vector: one parser trusts the standard
    EOCD, another trusts the ZIP64 override.

    Also raises an `IO.userError` containing
    `"ZIP64 EOCD64 record-size mismatch"` when the EOCD64 record's
    self-declared `size of zip64 end of central directory record` field
    (APPNOTE §4.3.14, at `bufPos + 4`) is not exactly `44` — the v1
    EOCD64 shape lean-zip produces and consumes. -/
private def findEndOfCentralDir (data : ByteArray) (baseOffset : Nat := 0)
    : IO (Option (Nat × Nat × Nat × Nat × Nat × Nat × Nat)) := do
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
  -- Capture raw standard-EOCD values for the ZIP64-override sentinel check
  -- below.  These must remain untouched across the override branch so the
  -- `unless` guards compare the original file-byte values, not the mutated
  -- ZIP64 values.
  let stdNumberOfThisDisk16   := Binary.readUInt16LE data (pos + 4)
  let stdDiskWhereCDStarts16  := Binary.readUInt16LE data (pos + 6)
  let stdNumEntriesThisDisk16 := Binary.readUInt16LE data (pos + 8)
  let stdTotalEntries16       := Binary.readUInt16LE data (pos + 10)
  let stdCdSize32             := Binary.readUInt32LE data (pos + 12)
  let stdCdOffset32           := Binary.readUInt32LE data (pos + 16)
  let mut cdSize := stdCdSize32.toNat
  let mut cdOffset := stdCdOffset32.toNat
  let mut totalEntries := stdTotalEntries16.toNat
  let mut numberOfThisDisk := stdNumberOfThisDisk16.toNat
  let mut diskWhereCDStarts := stdDiskWhereCDStarts16.toNat
  let mut numEntriesThisDisk := stdNumEntriesThisDisk16.toNat
  -- Check for ZIP64 EOCD Locator (20 bytes before standard EOCD)
  if pos >= 20 then
    if Binary.readUInt32LE data (pos - 20) == sigLocator64 then
      let eocd64Offset := (Binary.readUInt64LE data (pos - 12)).toNat
      -- Convert file-absolute offset to buffer-relative
      if eocd64Offset >= baseOffset then
        let bufPos := eocd64Offset - baseOffset
        if bufPos + 56 <= data.size then
          if Binary.readUInt32LE data bufPos == sigEOCD64 then
            -- EOCD64 self-declared record-size sanity (APPNOTE §4.3.14).
            -- For the v1 EOCD64 without an extensible data sector — the
            -- only shape lean-zip produces or consumes — this field must
            -- equal `SizeOfFixedFields + SizeOfVariableData - 12`, i.e.
            -- `44` (56 fixed bytes minus the 12 bytes of signature +
            -- size field).  Writer-side confirmation:
            -- `Zip/Archive.lean:142` hard-codes `44`.  A non-44 value is
            -- a parser-differential smuggling vector: lean-zip uses the
            -- fixed 56-byte layout, while a stricter parser trusts the
            -- self-declared length and reads past or short of that.
            let eocd64RecordSize := Binary.readUInt64LE data (bufPos + 4)
            unless eocd64RecordSize == 44 do
              throw (IO.userError
                s!"zip: ZIP64 EOCD64 record-size mismatch (size={eocd64RecordSize}, expected 44 for v1 EOCD64)")
            cdSize := (Binary.readUInt64LE data (bufPos + 40)).toNat
            cdOffset := (Binary.readUInt64LE data (bufPos + 48)).toNat
            totalEntries := (Binary.readUInt64LE data (bufPos + 32)).toNat
            numberOfThisDisk := (Binary.readUInt32LE data (bufPos + 16)).toNat
            diskWhereCDStarts := (Binary.readUInt32LE data (bufPos + 20)).toNat
            numEntriesThisDisk := (Binary.readUInt64LE data (bufPos + 24)).toNat
            -- ZIP64-override sentinel checks (APPNOTE §4.3.16).  Each guard
            -- permits either the sentinel (strict APPNOTE-compliant overflow
            -- encoding) or a numeric match against the ZIP64 override
            -- (producers such as Go's `archive/zip` emit ZIP64 with the real
            -- disk-number value `0` in the standard EOCD rather than
            -- `0xFFFF` — see `testdata/zip/interop/go-zip64.zip`). Rejection
            -- fires only when the standard field is both non-sentinel AND
            -- numerically disagrees with the ZIP64 override — the
            -- parser-differential smuggling vector.
            unless stdCdSize32 == val32Max ∨ stdCdSize32.toNat == cdSize do
              throw (IO.userError
                s!"zip: EOCD ZIP64-override mismatch: standard EOCD cdSize={stdCdSize32}, ZIP64 cdSize={cdSize} (expected sentinel {val32Max} or numeric match)")
            unless stdCdOffset32 == val32Max ∨ stdCdOffset32.toNat == cdOffset do
              throw (IO.userError
                s!"zip: EOCD ZIP64-override mismatch: standard EOCD cdOffset={stdCdOffset32}, ZIP64 cdOffset={cdOffset} (expected sentinel {val32Max} or numeric match)")
            unless stdTotalEntries16 == val16Max ∨ stdTotalEntries16.toNat == totalEntries do
              throw (IO.userError
                s!"zip: EOCD ZIP64-override mismatch: standard EOCD totalEntries={stdTotalEntries16}, ZIP64 totalEntries={totalEntries} (expected sentinel {val16Max} or numeric match)")
            unless stdNumberOfThisDisk16 == val16Max ∨ stdNumberOfThisDisk16.toNat == numberOfThisDisk do
              throw (IO.userError
                s!"zip: EOCD ZIP64-override mismatch: standard EOCD numberOfThisDisk={stdNumberOfThisDisk16}, ZIP64 numberOfThisDisk={numberOfThisDisk} (expected sentinel {val16Max} or numeric match)")
            unless stdDiskWhereCDStarts16 == val16Max ∨ stdDiskWhereCDStarts16.toNat == diskWhereCDStarts do
              throw (IO.userError
                s!"zip: EOCD ZIP64-override mismatch: standard EOCD diskWhereCDStarts={stdDiskWhereCDStarts16}, ZIP64 diskWhereCDStarts={diskWhereCDStarts} (expected sentinel {val16Max} or numeric match)")
            unless stdNumEntriesThisDisk16 == val16Max ∨ stdNumEntriesThisDisk16.toNat == numEntriesThisDisk do
              throw (IO.userError
                s!"zip: EOCD ZIP64-override mismatch: standard EOCD numEntriesThisDisk={stdNumEntriesThisDisk16}, ZIP64 numEntriesThisDisk={numEntriesThisDisk} (expected sentinel {val16Max} or numeric match)")
  return some (pos, cdOffset, cdSize, totalEntries, numberOfThisDisk, diskWhereCDStarts,
    numEntriesThisDisk)

/-- Validate the outer sub-field layout of a CD/LH extra-data blob
    (APPNOTE §4.5 *"Extensible Data Fields"*): each sub-field has a
    4-byte header `[headerId : UInt16] [dataSize : UInt16]` followed by
    exactly `dataSize` payload bytes, iterated until the blob is
    exhausted. Returns `false` if any sub-field's declared `dataSize`
    extends past the end of the blob, or if a trailing 1-3 byte partial
    header follows the last complete sub-field.

    This is a structural check run unconditionally on extra-data before
    `parseZip64Extra`. Without it, the `parseZip64Extra` loop silently
    `break`s on a malformed sub-field — leaving the anomaly invisible
    in the no-ZIP64-sentinel case (the caller skips `parseZip64Extra`
    entirely) and misattributed to ZIP64-field resolution in the
    sentinel case. A malformed sub-field header is a parser-differential
    smuggling vector independent of ZIP64. -/
private def validateExtraFieldStructure (extraData : ByteArray) : Bool := Id.run do
  let mut epos := 0
  while epos + 4 <= extraData.size do
    let dataSize := (Binary.readUInt16LE extraData (epos + 2)).toNat
    if epos + 4 + dataSize > extraData.size then return false
    epos := epos + 4 + dataSize
  return epos == extraData.size

/-- Detect APPNOTE §4.5 duplicate ZIP64 (`headerId == 0x0001`) blocks
    in a CD/LH extra-data area.  Returns `true` iff two or more 0x0001
    blocks are present.  Assumes `validateExtraFieldStructure` has
    already returned `true` for the same buffer; under that precondition
    every sub-field header is well-formed and the inner length guard is
    redundant but kept for defence in depth.  Closes the parser-
    differential vector where two well-formed 0x0001 blocks let a
    "first-wins" reader (lean-zip pre-fix) and a "last-wins" reader
    disagree on the resolved sizes/offset for the same bytes. -/
private def hasDuplicateZip64Extra (extraData : ByteArray) : Bool := Id.run do
  let mut epos := 0
  let mut seen := false
  while epos + 4 <= extraData.size do
    let dataSize := (Binary.readUInt16LE extraData (epos + 2)).toNat
    if epos + 4 + dataSize > extraData.size then break
    if Binary.readUInt16LE extraData epos == 0x0001 then
      if seen then return true
      seen := true
    epos := epos + 4 + dataSize
  return false

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
        fpos := fpos + 8
      -- APPNOTE §4.5.3: `dataSize` is exactly `8 * N` where N counts
      -- the sentinel-gated 32-bit fields; slack is a smuggling vector.
      if fpos != fieldEnd then return none
      break
    epos := epos + 4 + dataSize
  -- If any field needs ZIP64 but the extra field wasn't found, fail
  if !found && (stdUncomp == val32Max || stdComp == val32Max || stdOffset == val32Max) then
    return none
  return some (uncompSize, compSize, localOff)

/-- Parse central directory entries from a ZIP file.

    `cdOffset`/`cdSize` locate the CD inside `data` — for `listFromHandle`,
    `data` holds only the CD bytes and `cdOffset = 0`. `cdFileOffset` is
    the CD's position in the *source file*, which the per-entry
    `localOffset + 30 ≤ cdFileOffset` archive-layout guard compares
    against. -/
private def parseCentralDir (data : ByteArray)
    (cdOffset cdSize declaredEntries numberOfThisDisk diskWhereCDStarts
      entriesThisDisk cdFileOffset : Nat)
    : IO (Array Entry) := do
  -- EOCD disk-number sanity: lean-zip supports single-disk archives only.
  -- Writer-side confirmation: both fields are hard-coded to 0 (see the
  -- "disk number" comments at the ZIP64 and standard EOCD write sites
  -- around Zip/Archive.lean:145 and :158). The reader rejects nonzero
  -- values here — post-ZIP64-override — to close the cross-disk
  -- smuggling vector. The two fields are checked together and both
  -- values are reported to make attribution deterministic.
  unless numberOfThisDisk == 0 && diskWhereCDStarts == 0 do
    throw (IO.userError
      s!"zip: EOCD disk-number mismatch (numberOfThisDisk={numberOfThisDisk}, diskWhereCDStarts={diskWhereCDStarts}); lean-zip supports single-disk archives only")
  -- EOCD entry-count sanity: `numEntriesThisDisk` and `totalEntries` must
  -- agree on single-disk archives (the only shape lean-zip supports).
  -- Writer-side confirmation: both fields receive the same `numEntries`
  -- at the EOCD/ZIP64 write sites (see Zip/Archive.lean:146-147 and
  -- :160-161). Treat `declaredEntries` (post-ZIP64-override `totalEntries`)
  -- as authoritative and report `entriesThisDisk` as the disagreement,
  -- matching the direction of the sibling `totalEntries` check below.
  unless entriesThisDisk == declaredEntries do
    throw (IO.userError
      s!"zip: EOCD numEntriesThisDisk mismatch (this-disk={entriesThisDisk}, total={declaredEntries})")
  let mut entries : Array Entry := #[]
  let mut pos := cdOffset
  let cdEnd := cdOffset + cdSize
  while pos + 46 <= cdEnd do
    let sig := Binary.readUInt32LE data pos
    if sig != sigCentral then break
    let versionNeeded := Binary.readUInt16LE data (pos + 6)
    let flags := Binary.readUInt16LE data (pos + 8)
    let method := Binary.readUInt16LE data (pos + 10)
    let lastModTime := Binary.readUInt16LE data (pos + 12)
    let lastModDate := Binary.readUInt16LE data (pos + 14)
    let crc := Binary.readUInt32LE data (pos + 16)
    let stdCompSize := Binary.readUInt32LE data (pos + 20)
    let stdUncompSize := Binary.readUInt32LE data (pos + 24)
    let nameLen := (Binary.readUInt16LE data (pos + 28)).toNat
    let extraLen := (Binary.readUInt16LE data (pos + 30)).toNat
    let commentLen := (Binary.readUInt16LE data (pos + 32)).toNat
    -- Per-entry disk-number sanity: lean-zip supports single-disk archives
    -- only, so each CD entry's `diskNumberStart` (APPNOTE §4.4.11) must be
    -- `0`. Writer-side confirmation: the 46-byte CD header is
    -- `Binary.zeros`-initialised and `pos + 34` is never overwritten (see
    -- the "disk number start (34)" comment at the writer site around
    -- Zip/Archive.lean:121). Reject early — this is a metadata-only
    -- dimension and a parser-differential smuggling vector. Mirrors the
    -- archive-level EOCD disk-number check above.
    let diskNumberStart := Binary.readUInt16LE data (pos + 34)
    unless diskNumberStart == 0 do
      throw (IO.userError
        s!"zip: CD entry diskNumberStart mismatch (diskNumberStart={diskNumberStart}) for entry at CD offset {pos}; lean-zip supports single-disk archives only")
    -- APPNOTE §4.4.10: `internalFileAttributes` (CD +36, UInt16) has
    -- bit 0 defined as "apparent ASCII/text data"; bits 1 and 2 are
    -- "reserved for use by PKWARE"; remaining bits are "unused in
    -- version 1.0". lean-zip's writer emits zero here (the 46-byte CD
    -- header is `Binary.zeros`-initialised and the writer never
    -- overwrites `pos + 36` — see the "internal attrs (36)" comment at
    -- the writer site around Zip/Archive.lean:131). Info-ZIP legitimately
    -- sets bit 0 on apparent text files (interop checked against
    -- `testdata/zip/interop/`: go-unix, go-test, go-crc32 all use
    -- `0x0000` or `0x0001`), so preserve bit 0 and reject any reserved
    -- bit (1-15). A crafted archive with reserved bits set is either
    -- smuggled attribution data a lenient parser silently trusts, or a
    -- parser-differential vector where a strict reader rejects. Sibling
    -- of the PR #1759 CD+34 (diskNumberStart) and PR #1752 EOCD
    -- numEntriesThisDisk writer-invariant guards on the same fast-fail
    -- layer — this closes the CD+36 writer-zero column.
    let internalAttrs := Binary.readUInt16LE data (pos + 36)
    unless internalAttrs &&& 0xFFFE == 0 do
      throw (IO.userError
        s!"zip: CD entry internalAttrs reserved bits set (internalAttrs={internalAttrs}) for entry at CD offset {pos}")
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
    -- APPNOTE §4.4.3.2: `versionNeededToExtract` is a plain UInt16
    -- with no sentinel-gating; lean-zip handles only `20` (stored /
    -- deflate with ≤ 2 GiB sizes) and `45` (ZIP64). Any higher value
    -- indicates an unsupported feature (Deflate64, BZIP2, AES,
    -- LZMA/PPMd/XZ — see APPNOTE §4.4.3.2 for the full taxonomy), so
    -- reject at CD parse time. The existing CD/LH downgrade check in
    -- `readEntryData` (`"LH versionNeededToExtract exceeds CD"`, PR
    -- #1736) is one-sided and lets crafted archives with both sides
    -- claiming e.g. `51` (AES) through — this upper bound closes that
    -- gap. Writer-side confirmation: `writeLocalHeader` at
    -- Zip/Archive.lean:90 and `writeCentralHeader` at :117 both emit
    -- `if z64 then 45 else 20`, so legitimate archives never exceed
    -- this threshold. Sibling of PR #1801 (method allowlist): both
    -- guards are independent dimensions of the CD-parse early-reject
    -- story — method 0 with `versionNeeded = 51` is caught here but
    -- not by the allowlist; method 14 with `versionNeeded = 20` is
    -- caught by the allowlist but not here.
    unless versionNeeded ≤ 45 do
      throw (IO.userError
        s!"zip: unsupported versionNeededToExtract ({versionNeeded}) for {name} at CD offset {pos}; lean-zip supports values up to 45 (ZIP64)")
    -- APPNOTE §4.4.5: the compression `method` field is a plain UInt16
    -- with no sentinel-gating, so the allowlist check is safe to run
    -- pre-ZIP64-resolution. lean-zip implements only method 0 (stored)
    -- and method 8 (deflate); any other value triggers the late
    -- `"unsupported method"` guard in `readEntryData`, but only on the
    -- `Archive.extract` path. Reject early here so `Archive.list` also
    -- catches the anomaly and so the error message attributes the
    -- fault to the CD-parse stage. Writer-side confirmation: `create`
    -- emits only `method == 0` or `method == 8`
    -- (see `let method : UInt16 := if useDeflate then 8 else 0` at
    -- Zip/Archive.lean:192). The late `readEntryData` throw stays in
    -- place as defense-in-depth — unreachable for CD-parseable archives
    -- via the public API, but kept so the precedence-shift story is
    -- grep-discoverable.
    unless method == 0 ∨ method == 8 do
      throw (IO.userError
        s!"zip: unsupported compression method {method} for {name} (lean-zip supports method 0 (stored) and method 8 (deflate))")
    -- APPNOTE §4.4.4 bit 4: Enhanced Deflating. When set, method 8
    -- payloads use Deflate64 (64 KiB window, extended literal
    -- alphabet). Neither the FFI zlib path nor `Zip/Native/Inflate.lean`
    -- implements Deflate64; crafted method-8 payloads with bit 4 set
    -- decode as plain DEFLATE, producing attacker-controlled output
    -- that differs from a Deflate64-aware reader. Reject at CD parse.
    -- Writer-side: `writeCentralHeader` emits `0x0800` only (bit 11
    -- UTF-8), so lean-zip archives never set this bit. The check is
    -- unconditional on method: gating on `method == 8 ∧ bit 4` would
    -- leave a method-0-bit-4 smuggling vector open (stored entry with
    -- bit 4 set is out-of-invariant relative to lean-zip's own writer
    -- regardless of method).
    unless flags &&& 0x0010 == 0 do
      throw (IO.userError
        s!"zip: CD entry enhanced-deflating flag bit 4 set (flags={flags}) for {name} at CD offset {pos}; lean-zip does not support APPNOTE §4.4.4 Deflate64")
    -- Structural check runs unconditionally (APPNOTE §4.5) so the
    -- no-ZIP64-sentinel path also rejects extra-data whose sub-field
    -- declared `dataSize` overruns the blob. Without this, a malformed
    -- sub-field header in a non-ZIP64 entry is entirely invisible
    -- (`parseZip64Extra` is skipped) and in the ZIP64 case the anomaly
    -- would be misattributed as a missing-0x0001 block.
    -- The duplicate-0x0001 guard runs only when ZIP64 parsing is needed
    -- (some standard size/offset field is the sentinel) — APPNOTE §4.5
    -- forbids more than one ZIP64 extra block per entry, and lean-zip's
    -- `parseZip64Extra` would otherwise silently use the first match
    -- ("first-wins") while a "last-wins" parser would use the second.
    let extraData := data.extract (pos + 46 + nameLen) (pos + 46 + nameLen + extraLen)
    unless validateExtraFieldStructure extraData do
      throw (IO.userError s!"zip: malformed extra field for {name}")
    let (uncompSize, compSize, localOff) ←
      if stdCompSize == val32Max || stdUncompSize == val32Max || stdOffset == val32Max then
        if hasDuplicateZip64Extra extraData then
          throw (IO.userError s!"zip: duplicate ZIP64 extra field for {name}")
        match parseZip64Extra extraData stdUncompSize stdCompSize stdOffset with
        | some v => pure v
        | none => throw (IO.userError s!"zip: malformed ZIP64 extra field for {name}")
      else
        pure (stdUncompSize.toUInt64, stdCompSize.toUInt64, stdOffset.toUInt64)
    -- Archive-layout invariant at the per-entry granularity: every
    -- entry's local header (LH signature + 30-byte fixed header,
    -- APPNOTE §4.3.7) must be readable strictly before the CD start.
    -- APPNOTE §4.3.6 pins the layout as `[LH+data]* [CD] [EOCD]`; the
    -- sibling archive-level guard (`cdOffset + cdSize ≤ eocdPos`, see
    -- `cd-extends-past-eocd.zip`) closes the macro invariant, and this
    -- check closes the micro invariant where an entry's `localOffset`
    -- claims a position inside or past the CD region. Writer-side
    -- confirmation: every `writeLocalHeader` call in `create` precedes
    -- the CD block, so `localOffset + 30 ≤ cdOffset` is universally
    -- true for legitimate archives. Placed after ZIP64 resolution so
    -- the resolved `UInt64` `localOff` is checked (the sentinel
    -- `0xFFFFFFFF` would otherwise spuriously fire here for legitimate
    -- ZIP64 archives). `Archive.list` benefits most — without this
    -- guard the late `readEntryData` signature check
    -- (`"bad local header signature"`) is the only gate, and only on
    -- the extract path, leaving a parser-differential window open for
    -- `Archive.list`. Asymmetric-subtraction shape mirrors `SpanInFile`
    -- below to avoid `UInt64` wrap on crafted very-large `localOff`.
    let cdFileOff := cdFileOffset.toUInt64
    unless localOff ≤ cdFileOff ∧ 30 ≤ cdFileOff - localOff do
      throw (IO.userError
        s!"zip: entry local offset overlaps central directory for {name} (localOffset={localOff}, cdOffset={cdFileOffset})")
    -- APPNOTE §4.4.5: method 0 ("stored") means no compression, so
    -- `compressedSize == uncompressedSize` is a tautological invariant.
    -- The writer emits equal values for stored entries; crafted archives
    -- with mismatched sizes are malformed and would trigger the late
    -- generic `"size mismatch"` guard in `readEntryData` only after
    -- burning any `maxEntrySize` cap on I/O.  Reject early here so
    -- `Archive.list` also catches the anomaly and so the error message
    -- attributes the fault to the stored invariant.  Placed after the
    -- ZIP64 resolution so the resolved `UInt64` values are checked, not
    -- the 0xFFFFFFFF sentinels (which would spuriously fail the
    -- equality for legitimate ZIP64-stored archives).
    if method == 0 then
      unless compSize == uncompSize do
        throw (IO.userError
          s!"zip: stored-method size mismatch for {name} (method=0, compressedSize={compSize}, uncompressedSize={uncompSize})")
    entries := entries.push {
      path := name
      compressedSize := compSize
      uncompressedSize := uncompSize
      crc32 := crc
      method := method
      localOffset := localOff
      flags := flags
      versionNeeded := versionNeeded
      lastModTime := lastModTime
      lastModDate := lastModDate
    }
    pos := pos + 46 + nameLen + extraLen + commentLen
  unless entries.size == declaredEntries do
    throw (IO.userError
      s!"zip: EOCD totalEntries mismatch (EOCD={declaredEntries}, parsed={entries.size})")
  return entries

/-- Check that a read span `[offset, offset + length)` lies entirely within a
    file whose size is `fileSize`. Throws a descriptive `IO.userError` if
    `offset > fileSize`, if `offset + length` would overflow `UInt64`, or if
    `offset + length > fileSize`. The overflow case is subsumed by comparing
    `length` against the saturating remainder `fileSize - offset`, which only
    takes a meaningful value once `offset ≤ fileSize`. -/
private def assertSpanInFile (fileSize offset length : UInt64) (what : String) : IO Unit := do
  if offset > fileSize then
    throw (IO.userError
      s!"zip: {what} offset ({offset}) exceeds file size ({fileSize})")
  let remaining := fileSize - offset
  if length > remaining then
    throw (IO.userError
      s!"zip: {what} extends past end of file (offset={offset}, length={length}, fileSize={fileSize})")

/-- `SpanInFile fileSize offset length` states that the half-open byte range
    `[offset, offset + length)` lies inside a file of size `fileSize`, with
    overflow-safe arithmetic on `UInt64`.

    Mirrors the two-check shape of `assertSpanInFile`: `offset ≤ fileSize`
    first, then `length ≤ fileSize - offset`, where the subtraction is the
    saturating remainder (well-defined once `offset ≤ fileSize`). Do NOT
    restate this as `offset + length ≤ fileSize` — `UInt64` addition wraps
    silently on overflow, which the asymmetric form exists to avoid. -/
def SpanInFile (fileSize offset length : UInt64) : Prop :=
  offset ≤ fileSize ∧ length ≤ fileSize - offset

instance (fileSize offset length : UInt64) :
    Decidable (SpanInFile fileSize offset length) :=
  inferInstanceAs (Decidable (_ ∧ _))

@[simp] theorem SpanInFile_iff {fileSize offset length : UInt64} :
    SpanInFile fileSize offset length ↔
      offset ≤ fileSize ∧ length ≤ fileSize - offset := Iff.rfl

/-- Helper: an `IO Unit` action that evaluates to `EST.Out.error _ _` at
    every `Void IO.RealWorld` state cannot equal `pure ()`. Used to discharge
    the `assertSpanInFile = pure ()` hypothesis once a guard has been shown
    to fire, by evaluating both sides at an arbitrary state. -/
private theorem io_ne_pure_of_state_error
    {x : IO Unit} {e : IO.Error}
    (hx : ∀ s : Void IO.RealWorld, x s = EST.Out.error e s) :
    x ≠ pure () := fun h => by
  have ⟨s⟩ : Nonempty (Void IO.RealWorld) := Void.instNonempty
  have happ : EST.Out.error (σ := IO.RealWorld) (α := Unit) e s = EST.Out.ok () s := by
    rw [← hx s]; exact congrFun h s
  cases happ

/-- Forward reduction: if the span is valid then `assertSpanInFile` is
    `pure ()`. Both `if` guards fall through to the `else` branch and the
    residual `pure PUnit.unit >>= fun _ => pure PUnit.unit` reduces to
    `pure ()` definitionally. -/
private theorem assertSpanInFile_eq_pure_of_spanInFile
    {fileSize offset length : UInt64} {what : String}
    (h : SpanInFile fileSize offset length) :
    assertSpanInFile fileSize offset length what = pure () := by
  obtain ⟨h1, h2⟩ := h
  unfold assertSpanInFile
  rw [if_neg (UInt64.not_lt.mpr h1), if_neg (UInt64.not_lt.mpr h2)]
  rfl

/-- Backward reduction: success of `assertSpanInFile` implies the pure
    predicate `SpanInFile` holds. For each guard, contraposition reduces
    `assertSpanInFile` to an action whose state-level value is
    `EST.Out.error`, which `io_ne_pure_of_state_error` rules out. -/
private theorem spanInFile_of_assertSpanInFile_succeeds
    {fileSize offset length : UInt64} {what : String}
    (h : assertSpanInFile fileSize offset length what = pure ()) :
    SpanInFile fileSize offset length := by
  have h1 : offset ≤ fileSize := by
    refine Decidable.by_contra fun h1 => ?_
    unfold assertSpanInFile at h
    rw [if_pos (UInt64.not_le.mp h1)] at h
    exact io_ne_pure_of_state_error (e := _) (fun _ => rfl) h
  refine ⟨h1, ?_⟩
  refine Decidable.by_contra fun h2 => ?_
  unfold assertSpanInFile at h
  rw [if_neg (UInt64.not_lt.mpr h1), if_pos (UInt64.not_le.mp h2)] at h
  exact io_ne_pure_of_state_error (e := _) (fun _ => rfl) h

/-- `Nat`-level consequence of `SpanInFile`: the end-offset of the span is
    file-bounded. Caller-facing arithmetic lemma — future bounded-read
    reasoning cites this without re-deriving the `UInt64` arithmetic. -/
theorem SpanInFile.toNat_add_le
    {fileSize offset length : UInt64}
    (h : SpanInFile fileSize offset length) :
    offset.toNat + length.toNat ≤ fileSize.toNat := by
  obtain ⟨h1, h2⟩ := h
  have h1n : offset.toNat ≤ fileSize.toNat := UInt64.le_iff_toNat_le.mp h1
  have h2n : length.toNat ≤ (fileSize - offset).toNat := UInt64.le_iff_toNat_le.mp h2
  rw [UInt64.toNat_sub_of_le _ _ h1] at h2n
  omega

/-- `Nat`-level consequence of `SpanInFile`: the span length is bounded by the
    remaining file size past the span's start offset. Caller-facing
    arithmetic lemma — future bounded-read reasoning cites this without
    re-deriving the `UInt64` saturating subtraction. -/
theorem SpanInFile.toNat_length_le_remaining
    {fileSize offset length : UInt64}
    (h : SpanInFile fileSize offset length) :
    length.toNat ≤ fileSize.toNat - offset.toNat := by
  obtain ⟨h1, h2⟩ := h
  have h2n : length.toNat ≤ (fileSize - offset).toNat := UInt64.le_iff_toNat_le.mp h2
  rwa [UInt64.toNat_sub_of_le _ _ h1] at h2n

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

/-- Validate a read span against `fileSize`, seek to `offset`, and read exactly
    `length` bytes. The one-shot "validate the span, then read" primitive that
    `Archive.readEntryData`'s three open-coded `assertSpanInFile` + seek +
    `readExact` chains implement today.

    Precondition: `offset + length ≤ fileSize`. On violation, throws
    `IO.userError` with one of two substrings (sourced from `assertSpanInFile`):
    `"offset (…) exceeds file size (…)"` if `offset > fileSize`, or
    `"extends past end of file"` if the span runs past the tail. If the span is
    valid but the underlying handle returns fewer than `length` bytes, throws
    with substring `"short read for {what}"` (sourced from `readExact`). The
    addressable-range guard (`"exceeds addressable range"`) also fires here for
    any `length` whose `Nat` value does not round-trip through `USize`.

    Callers that have already validated the span and only need the read primitive
    should use `readBoundedExactFromHandle` instead. Cross-reference:
    `SECURITY_INVENTORY.md` § "Local guard inventory for `Handle.read` and
    `Stream.read`". -/
def readBoundedSpanFromHandle (h : IO.FS.Handle)
    (fileSize offset length : UInt64) (what : String) : IO ByteArray := do
  assertSpanInFile fileSize offset length what
  Handle.seek h offset
  readExact h length.toNat what

/-- Bounded-length `readExact` for callers that have validated their span
    separately (e.g. after seeking within a span they already confirmed lies
    inside the file). Asserts `length.toUSize.toNat = length` before any
    `Handle.read`; on violation throws `IO.userError` with substring
    `"exceeds addressable range"`. Short reads surface the
    `"short read for {what}"` substring from `readExact`. This is the "already-
    validated span" cousin of `readBoundedSpanFromHandle`. Cross-reference:
    `SECURITY_INVENTORY.md` § "Local guard inventory for `Handle.read` and
    `Stream.read`". -/
def readBoundedExactFromHandle (h : IO.FS.Handle)
    (length : UInt64) (what : String) : IO ByteArray :=
  readExact h length.toNat what

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
  let some (_, cdOffset, cdSize, totalEntries, numberOfThisDisk, diskWhereCDStarts,
      numEntriesThisDisk) ←
      findEndOfCentralDir tail tailStart
    | throw (IO.userError "zip: cannot find end of central directory")
  unless cdOffset + cdSize <= fileSize do
    throw (IO.userError "zip: central directory extends beyond file")
  if maxCentralDirSize > 0 && cdSize > maxCentralDirSize then
    throw (IO.userError s!"zip: central directory too large ({cdSize} bytes, limit {maxCentralDirSize})")
  -- Read just the central directory
  Handle.seek h cdOffset.toUInt64
  let cdBuf ← readExact h cdSize "central directory"
  parseCentralDir cdBuf 0 cdSize totalEntries numberOfThisDisk diskWhereCDStarts
    numEntriesThisDisk cdOffset

/-- Read an entry's decompressed data from a file handle by seeking to its local header.
    `maxEntrySize` limits decompressed entry size; `0` means no limit on the FFI
    backend. Both public extractors default `maxEntrySize` to `1 GiB` and
    always pass the value through explicitly, so this helper has no default.
    When `useNative` is true, uses the pure Lean DEFLATE decompressor and CRC-32. -/
private def readEntryData (h : IO.FS.Handle) (entry : Entry) (label : String)
    (maxEntrySize : UInt64) (useNative : Bool := false) : IO ByteArray := do
  if maxEntrySize > 0 && entry.uncompressedSize > maxEntrySize then
    throw (IO.userError s!"zip: entry '{label}' uncompressed size ({entry.uncompressedSize}) exceeds limit ({maxEntrySize})")
  -- Span-validate every attacker-controlled read against actual file size.
  let fileSize ← Handle.fileSize h
  let localHdr ← readBoundedSpanFromHandle h fileSize entry.localOffset 30
    s!"local header for {label}"
  unless Binary.readUInt32LE localHdr 0 == sigLocal do
    throw (IO.userError s!"zip: bad local header signature for {label}")
  -- Parse the remaining local-header fields for CD/LH consistency checks.
  -- Offsets per PKZIP APPNOTE Appendix D: 4=versionNeeded, 6=flags,
  -- 8=method, 14=crc, 18=stdLocalCompSize, 22=stdLocalUncompSize,
  -- 26=nameLen, 28=extraLen.
  let localVersion := Binary.readUInt16LE localHdr 4
  let localFlags := Binary.readUInt16LE localHdr 6
  let localMethod := Binary.readUInt16LE localHdr 8
  let localModTime := Binary.readUInt16LE localHdr 10
  let localModDate := Binary.readUInt16LE localHdr 12
  let localCrc := Binary.readUInt32LE localHdr 14
  let stdLocalCompSize := Binary.readUInt32LE localHdr 18
  let stdLocalUncompSize := Binary.readUInt32LE localHdr 22
  let nameLen := (Binary.readUInt16LE localHdr 26).toNat
  let extraLen := (Binary.readUInt16LE localHdr 28).toNat
  -- Verify the compressed-payload span lies within the file before the
  -- `readBoundedSpanFromHandle` calls below are driven by untrusted metadata.
  -- `nameLen + extraLen` is bounded by `2 * UInt16.max`, so `headerAndNames`
  -- cannot overflow `UInt64`; this assertion bounds `entry.compressedSize`
  -- against the remaining file tail. The `readBoundedSpanFromHandle` for the
  -- compressed payload re-asserts the same span internally — that redundancy
  -- is harmless and keeps the helper interface uniform across the three reads.
  let headerAndNames : UInt64 := 30 + nameLen.toUInt64 + extraLen.toUInt64
  assertSpanInFile fileSize (entry.localOffset + headerAndNames)
    entry.compressedSize s!"local data span for {label}"
  let nameAndExtra ← readBoundedSpanFromHandle h fileSize
    (entry.localOffset + 30) (nameLen.toUInt64 + extraLen.toUInt64)
    s!"local name+extra for {label}"
  -- Resolve the effective local sizes through any ZIP64 local extra block.
  -- Local headers do not carry the file-offset field, so pass `stdOffset = 0`
  -- to `parseZip64Extra` and discard the offset slot it returns.
  -- Structural check on sub-field layout runs unconditionally (APPNOTE §4.5)
  -- so the no-ZIP64-sentinel LH path also rejects extra-data whose sub-field
  -- declared `dataSize` overruns the blob — mirrors the CD-side check.
  let localExtra := nameAndExtra.extract nameLen (nameLen + extraLen)
  unless validateExtraFieldStructure localExtra do
    throw (IO.userError s!"zip: malformed local extra field for {label}")
  let (localUncompSize, localCompSize, _) ←
    if stdLocalCompSize == val32Max || stdLocalUncompSize == val32Max then
      -- Mirrors the CD-side duplicate-0x0001 guard in `parseCentralDir`:
      -- APPNOTE §4.5 forbids more than one ZIP64 extra-field block per
      -- entry on the LH side as well.
      if hasDuplicateZip64Extra localExtra then
        throw (IO.userError s!"zip: duplicate ZIP64 local extra field for {label}")
      match parseZip64Extra localExtra stdLocalUncompSize stdLocalCompSize 0 with
      | some v => pure v
      | none => throw (IO.userError s!"zip: truncated ZIP64 local extra field for {label}")
    else
      pure (stdLocalUncompSize.toUInt64, stdLocalCompSize.toUInt64, (0 : UInt64))
  -- CD vs LH consistency. Method must always agree.  When bit 3 of the local
  -- flags ("data descriptor present") is set, the LH crc/compSize/uncompSize
  -- fields are legitimately zero with the real values trailing the payload in
  -- a data descriptor — defer crc/size checks to `actualCrc` below in that
  -- case (we do not parse the data descriptor itself today).
  -- Flag bits other than bit 3 are checked below for CD/LH consistency.
  unless localMethod == entry.method do
    throw (IO.userError
      s!"zip: method mismatch between CD and local header for {label} (CD={entry.method}, LH={localMethod})")
  -- Flags must agree on every bit except bit 3 (data-descriptor presence,
  -- which is a per-segment local concern), so XOR-mask out bit 3 before
  -- comparing. A mismatch on bit 11 (UTF-8 name) in particular is a
  -- known smuggling vector — the CD-derived `Entry.path` we already
  -- parsed used CD's bit-11 setting; if the LH disagrees, downstream
  -- consumers that re-parse the LH would get a different name.
  unless (localFlags &&& dataDescriptorBitMask) == (entry.flags &&& dataDescriptorBitMask) do
    throw (IO.userError
      s!"zip: flags mismatch between CD and local header for {label} (CD={entry.flags}, LH={localFlags})")
  -- One-sided CD/LH versionNeededToExtract check.  Rejects LH claiming a
  -- higher version than CD (a capability-smuggle vector — e.g. LH=45
  -- "ZIP64 features required" alongside CD=20, bypassing readers that
  -- feature-gate on the CD).  The converse (CD > LH) is legitimate: Go's
  -- `archive/zip` and CPython's `zipfile` emit ZIP64 archives whose LH
  -- sizes fit in 32 bits with `LH.versionNeeded=20` while the CD carries
  -- a ZIP64 size extra with `CD.versionNeeded=45`.
  unless localVersion ≤ entry.versionNeeded do
    throw (IO.userError
      s!"zip: LH versionNeededToExtract ({localVersion}) exceeds CD versionNeededToExtract ({entry.versionNeeded}) for {label}")
  -- DOS last-modified time/date (APPNOTE §4.4.6) must agree between CD
  -- and LH.  Unlike crc/compSize/uncompSize, these fields are metadata
  -- and are NOT legitimately zeroed by the data-descriptor bit — keep
  -- the check ungated.  A single combined `unless` because the two
  -- fields are physically adjacent (LH +10/+12, CD +12/+14) and
  -- semantically a single DOS timestamp pair.
  unless localModTime == entry.lastModTime ∧
         localModDate == entry.lastModDate do
    throw (IO.userError
      s!"zip: lastModTime/Date mismatch between CD and local header for {label} (CD time={entry.lastModTime}, date={entry.lastModDate}; LH time={localModTime}, date={localModDate})")
  let usesDataDescriptor := (localFlags &&& 0x0008) != 0
  unless usesDataDescriptor do
    unless localCompSize == entry.compressedSize do
      throw (IO.userError
        s!"zip: compressedSize mismatch between CD and local header for {label} (CD={entry.compressedSize}, LH={localCompSize})")
    unless localUncompSize == entry.uncompressedSize do
      throw (IO.userError
        s!"zip: uncompressedSize mismatch between CD and local header for {label} (CD={entry.uncompressedSize}, LH={localUncompSize})")
    unless localCrc == entry.crc32 do
      throw (IO.userError
        s!"zip: crc32 mismatch between CD and local header for {label} (CD={entry.crc32}, LH={localCrc})")
  let compData ← readBoundedSpanFromHandle h fileSize
    (entry.localOffset + headerAndNames) entry.compressedSize
    s!"compressed data for {label}"
  let fileData ←
    if entry.method == 0 then pure compData
    else if entry.method == 8 then
      if useNative then
        -- `Zip.Native.Inflate.inflate` treats `0` as "reject any non-empty
        -- output", unlike the FFI path where `0` means unlimited. Callers
        -- that opt into `maxEntrySize := 0` for unlimited FFI decompression
        -- therefore get an immediate rejection on the native backend.
        match Zip.Native.Inflate.inflate compData maxEntrySize.toNat with
        | .ok data => pure data
        | .error msg => throw (IO.userError s!"zip: native inflate failed for {label}: {msg}")
      else RawDeflate.decompress compData maxEntrySize
    else throw (IO.userError s!"zip: unsupported method {entry.method} for {label}")
  let actualCrc :=
    if useNative then Crc32.Native.crc32 0 fileData
    else Checksum.crc32 0 fileData
  unless actualCrc == entry.crc32 do
    throw (IO.userError s!"zip: CRC32 mismatch for {label}: expected {entry.crc32}, got {actualCrc}")
  unless fileData.size.toUInt64 == entry.uncompressedSize do
    throw (IO.userError s!"zip: size mismatch for {label}")
  return fileData

/-- List entries in a ZIP archive. Memory: O(65KB + central directory metadata).
    `maxCentralDirSize` limits the central directory allocation; default 64 MiB,
    `0` means unlimited (bomb-unsafe for untrusted input). Overflow raises
    `IO.userError` containing `"zip: central directory too large"`.
    See `SECURITY_INVENTORY.md` *Decompression Limit Inventory*. -/
def list (inputPath : System.FilePath) (maxCentralDirSize : Nat := 67108864) : IO (Array Entry) :=
  IO.FS.withFile inputPath .read (listFromHandle · maxCentralDirSize)

/-- Extract a ZIP archive to an output directory.
    Memory: O(65KB + central directory + largest single file).

    `maxCentralDirSize` limits the central directory allocation; default 64 MiB,
    `0` means unlimited. Overflow raises `IO.userError` containing
    `"zip: central directory too large"`.

    `maxEntrySize` limits each entry's decompressed size. Default `1 GiB`
    per entry; pass `0` to opt out into unlimited mode on the FFI backend.
    Overflow raises `IO.userError` containing
    `"zip: entry '…' uncompressed size (…) exceeds limit (…)"`.

    `maxTotalSize` (when non-zero) caps the sum of decompressed bytes across
    all entries written by this extraction. Default `0` means no whole-archive
    cap; rely on `maxEntrySize` for per-entry bounding. Overflow raises
    `IO.userError` containing
    `"zip: total extracted size (…) exceeds whole-archive limit (…)"`.
    See `SECURITY_INVENTORY.md` *Decompression Limit Inventory*.

    When `useNative` is true, uses pure Lean decompression (no C FFI).
    See `SECURITY_INVENTORY.md` *Decompression Limit Inventory*. -/
def extract (inputPath : System.FilePath) (outDir : System.FilePath)
    (maxCentralDirSize : Nat := 67108864) (maxEntrySize : UInt64 := 1024 * 1024 * 1024)
    (maxTotalSize : UInt64 := 0)
    (useNative : Bool := false) : IO Unit := do
  IO.FS.withFile inputPath .read fun h => do
    let entries ← listFromHandle h maxCentralDirSize
    let totalRef ← IO.mkRef (0 : UInt64)
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
      -- Whole-archive running-total check: fires before any payload bytes are
      -- written for this entry. The invariant `running ≤ maxTotalSize` keeps
      -- `maxTotalSize - running` well-defined in UInt64 arithmetic.
      if maxTotalSize > 0 then
        let running ← totalRef.get
        if maxTotalSize - running < entry.uncompressedSize then
          throw (IO.userError s!"zip: total extracted size ({entry.uncompressedSize.toNat + running.toNat}) exceeds whole-archive limit ({maxTotalSize})")
      let outPath := outDir / entry.path
      if let some parent := outPath.parent then
        IO.FS.createDirAll parent
      let fileData ← readEntryData h entry entry.path maxEntrySize useNative
      IO.FS.writeBinFile outPath fileData
      totalRef.modify (· + entry.uncompressedSize)

/-- Extract a single file from a ZIP archive by name.
    Memory: O(65KB + central directory + target file).

    `maxCentralDirSize` limits the central directory allocation; default 64 MiB,
    `0` means unlimited. Overflow raises `IO.userError` containing
    `"zip: central directory too large"`.

    `maxEntrySize` limits the decompressed entry size. Default `1 GiB`
    per entry; pass `0` to opt out into unlimited mode on the FFI backend.
    Overflow raises `IO.userError` containing
    `"zip: entry '…' uncompressed size (…) exceeds limit (…)"`.

    When `useNative` is true, uses pure Lean decompression (no C FFI).
    See `SECURITY_INVENTORY.md` *Decompression Limit Inventory*. -/
def extractFile (inputPath : System.FilePath) (filename : String)
    (maxCentralDirSize : Nat := 67108864) (maxEntrySize : UInt64 := 1024 * 1024 * 1024)
    (useNative : Bool := false) : IO ByteArray := do
  IO.FS.withFile inputPath .read fun h => do
    let entries ← listFromHandle h maxCentralDirSize
    let some entry := entries.find? (·.path == filename)
      | throw (IO.userError s!"zip: file not found: {filename}")
    readEntryData h entry filename maxEntrySize useNative

end Archive
