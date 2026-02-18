import Zip.Binary
import Zip.Gzip

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
/-- GNU typeflag for long name. -/
def typeGnuLongName : UInt8 := 0x4C  -- 'L'
/-- GNU typeflag for long link. -/
def typeGnuLongLink : UInt8 := 0x4B  -- 'K'
/-- PAX typeflag for per-file extended header. -/
def typePaxExtended : UInt8 := 0x78  -- 'x'
/-- PAX typeflag for global extended header. -/
def typePaxGlobal : UInt8 := 0x67  -- 'g'

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

/-- Read a numeric field from a tar header. Handles both octal ASCII (standard)
    and GNU base-256 encoding (high bit set in first byte). -/
@[noinline] def readNumeric (data : ByteArray) (offset : Nat) (len : Nat) : UInt64 := Id.run do
  if len == 0 then return 0
  let firstByte := data[offset]!
  -- GNU base-256: if high bit is set, remaining bytes are big-endian binary
  if firstByte &&& 0x80 != 0 then
    let mut result : UInt64 := (firstByte &&& 0x7F).toUInt64
    for i in [1:len] do
      result := (result <<< 8) ||| data[offset + i]!.toUInt64
    return result
  -- Standard octal ASCII
  return Binary.readOctal data offset len

/-- Parse PAX extended header records from data.
    Format: `<length> <key>=<value>\n` where length includes itself.
    Returns an array of (key, value) pairs. -/
@[noinline] def parsePaxRecords (data : ByteArray) : Array (String × String) := Id.run do
  let mut records : Array (String × String) := #[]
  let mut pos := 0
  while pos < data.size do
    -- Read the decimal length field (digits only, terminated by space)
    let mut lenVal := 0
    let mut lenEnd := pos
    let mut validLen := true
    while lenEnd < data.size do
      let b := data[lenEnd]!
      if b == ' '.toNat.toUInt8 then
        lenEnd := lenEnd + 1
        break
      if b >= '0'.toNat.toUInt8 && b <= '9'.toNat.toUInt8 then
        lenVal := lenVal * 10 + (b - '0'.toNat.toUInt8).toNat
      else
        validLen := false
      lenEnd := lenEnd + 1
    if !validLen || lenVal == 0 then break
    -- The record is lenVal bytes total from pos
    let recordEnd := pos + lenVal
    if recordEnd > data.size then break
    -- Find '=' separator
    let mut eqPos := lenEnd
    while eqPos < recordEnd do
      if data[eqPos]! == '='.toNat.toUInt8 then break
      eqPos := eqPos + 1
    if eqPos < recordEnd then
      let key := String.fromUTF8! (data.extract lenEnd eqPos)
      -- Value runs from after '=' to before trailing newline
      let valueEnd := if recordEnd > 0 && data[recordEnd - 1]! == '\n'.toNat.toUInt8
                       then recordEnd - 1 else recordEnd
      let value := String.fromUTF8! (data.extract (eqPos + 1) valueEnd)
      records := records.push (key, value)
    pos := recordEnd
  return records

/-- Apply PAX extended header overrides to an entry. -/
def applyPaxOverrides (entry : Entry) (records : Array (String × String)) : Entry := Id.run do
  let mut e := entry
  for (key, value) in records do
    match key with
    | "path" => e := { e with path := value }
    | "linkpath" => e := { e with linkname := value }
    | "size" =>
      let mut n : UInt64 := 0
      for c in value.toList do
        if c >= '0' && c <= '9' then
          n := n * 10 + (c.toNat - '0'.toNat).toUInt64
      e := { e with size := n }
    | "mtime" =>
      -- PAX mtime can be decimal (e.g. "1234567890.123456789"), take integer part
      let intPart := (value.splitOn ".").head!
      let mut n : UInt64 := 0
      for c in intPart.toList do
        if c >= '0' && c <= '9' then
          n := n * 10 + (c.toNat - '0'.toNat).toUInt64
      e := { e with mtime := n }
    | "uid" =>
      let mut n : UInt32 := 0
      for c in value.toList do
        if c >= '0' && c <= '9' then
          n := n * 10 + (c.toNat - '0'.toNat).toUInt32
      e := { e with uid := n }
    | "gid" =>
      let mut n : UInt32 := 0
      for c in value.toList do
        if c >= '0' && c <= '9' then
          n := n * 10 + (c.toNat - '0'.toNat).toUInt32
      e := { e with gid := n }
    | "uname" => e := { e with uname := value }
    | "gname" => e := { e with gname := value }
    | _ => pure ()  -- ignore unknown keys
  return e

/-- Compute padding needed to reach next 512-byte boundary. -/
def paddingFor (size : UInt64) : Nat :=
  let rem := size.toNat % 512
  if rem == 0 then 0 else 512 - rem

/-- Read entry data from a stream (for GNU long name / PAX headers). -/
private partial def readEntryData (input : IO.FS.Stream) (size : Nat) : IO ByteArray := do
  let mut result := ByteArray.empty
  let mut remaining := size
  while remaining > 0 do
    let toRead := min remaining 65536
    let chunk ← input.read toRead.toUSize
    if chunk.isEmpty then
      throw (IO.userError "tar: unexpected end of archive reading entry data")
    result := result ++ chunk
    remaining := remaining - chunk.size
  -- Skip padding
  let pad := paddingFor size.toUInt64
  if pad > 0 then
    let padData ← input.read pad.toUSize
    if padData.size < pad then
      throw (IO.userError "tar: unexpected end of archive reading padding")
  return result

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

-- Helper to write fields into a header at a given offset
private def writeField (hdr : ByteArray) (offset : Nat) (field : ByteArray) : ByteArray := Id.run do
  let mut h := hdr
  for i in [:field.size] do
    h := h.set! (offset + i) field[i]!
  return h

-- Maximum value representable in an 11-digit octal field (used by size/mtime)
private def maxOctalValue : UInt64 := 0o77777777777  -- 8589934591

/-- Build a 512-byte UStar header. If `pathOverride` is provided, it is used instead of
    `entry.path` (which may exceed UStar limits if a PAX header precedes this). -/
def buildHeader (entry : Entry) (pathOverride : Option (String × String) := none) : IO ByteArray := do
  let (pfx, name) ← match pathOverride with
    | some pn => pure pn
    | none =>
      match splitPath entry.path with
      | some pn => pure pn
      | none => throw (IO.userError s!"tar: path too long: {entry.path}")
  -- Start with 512 zero bytes
  let mut hdr := Binary.zeros 512
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

/-- Build a single PAX record: `<length> <key>=<value>\n`.
    The length field includes itself, requiring iterative computation. -/
@[noinline] def buildPaxRecord (key : String) (value : String) : ByteArray := Id.run do
  let content := s!"{key}={value}\n".toUTF8
  -- Length field includes itself + space + content
  -- Start with estimate, iterate until stable
  let mut lenStr := s!"{content.size + 2}"  -- estimate: "N "
  for _ in [:5] do  -- converges in ≤3 iterations
    let total := lenStr.toUTF8.size + 1 + content.size  -- lenStr + " " + content
    let newLenStr := s!"{total}"
    if newLenStr == lenStr then break
    lenStr := newLenStr
  return s!"{lenStr} ".toUTF8 ++ content

/-- Determine if a PAX extended header is needed for an entry, and if so,
    return the PAX data and a suitable truncated path for the UStar header. -/
def needsPaxHeader (entry : Entry) : Option ByteArray := Id.run do
  let mut records := ByteArray.empty
  let mut needed := false
  -- Path too long for UStar?
  if splitPath entry.path |>.isNone then
    records := records ++ buildPaxRecord "path" entry.path
    needed := true
  -- Linkname too long?
  if entry.linkname.utf8ByteSize > 100 then
    records := records ++ buildPaxRecord "linkpath" entry.linkname
    needed := true
  -- Size exceeds octal range?
  if entry.size > maxOctalValue then
    records := records ++ buildPaxRecord "size" s!"{entry.size.toNat}"
    needed := true
  -- Mtime exceeds octal range?
  if entry.mtime > maxOctalValue then
    records := records ++ buildPaxRecord "mtime" s!"{entry.mtime.toNat}"
    needed := true
  if needed then return some records else return none

/-- Build a PAX extended header entry (typeflag 'x') for the given PAX data. -/
def buildPaxEntry (paxData : ByteArray) (entryPath : String) : IO ByteArray := do
  -- Truncate the entry path to fit in UStar name field
  let paxName :=
    let truncated := if entryPath.utf8ByteSize > 80 then
      -- Take first 80 bytes worth of the path
      String.fromUTF8! (entryPath.toUTF8.extract 0 80)
    else entryPath
    s!"PaxHeader/{truncated}"
  let paxEntry : Entry := {
    path := (if paxName.utf8ByteSize > 100 then
      String.fromUTF8! (paxName.toUTF8.extract 0 100) else paxName)
    size := paxData.size.toUInt64
    mode := 0o644
    typeflag := typePaxExtended
  }
  let paxHdr ← buildHeader paxEntry
  let pad := paddingFor paxData.size.toUInt64
  return paxHdr ++ paxData ++ Binary.zeros pad

/-- Verify the tar header checksum. Returns true if valid. -/
@[noinline] def verifyChecksum (block : ByteArray) : Bool := Id.run do
  let storedChksum := Binary.readOctal block hdrChksum.1 hdrChksum.2
  let computed := computeChecksum block
  return storedChksum == computed.toUInt64

/-- Parse a 512-byte header block into an Entry. Returns `none` for zero blocks.
    Validates magic and checksum; throws on malformed headers. -/
def parseHeader (block : ByteArray) : IO (Option Entry) := do
  -- Check for zero block (end of archive)
  let allZero := Id.run do
    let mut z := true
    for i in [:512] do
      if block[i]! != 0 then
        z := false
        break
    return z
  if allZero then return none
  -- Validate checksum
  unless verifyChecksum block do
    throw (IO.userError "tar: header checksum mismatch")
  -- Validate UStar magic (accept both "ustar\0" and "ustar " for compatibility)
  let magic := Binary.readString block hdrMagic.1 hdrMagic.2
  unless magic == "ustar" do
    throw (IO.userError s!"tar: unsupported format (magic: {magic})")
  let name := Binary.readString block hdrName.1 hdrName.2
  let pfx := Binary.readString block hdrPrefix.1 hdrPrefix.2
  let fullPath := if pfx.isEmpty then name else pfx ++ "/" ++ name
  return some {
    path := fullPath
    size := readNumeric block hdrSize.1 hdrSize.2
    mode := (Binary.readOctal block hdrMode.1 hdrMode.2).toUInt32
    mtime := readNumeric block hdrMtime.1 hdrMtime.2
    uid := (Binary.readOctal block hdrUid.1 hdrUid.2).toUInt32
    gid := (Binary.readOctal block hdrGid.1 hdrGid.2).toUInt32
    typeflag := block[hdrTypeflag.1]!
    linkname := Binary.readString block hdrLinkname.1 hdrLinkname.2
    uname := Binary.readString block hdrUname.1 hdrUname.2
    gname := Binary.readString block hdrGname.1 hdrGname.2
  }

/-- Check if a path is safe for extraction (no `..` segments, not absolute). -/
private def isPathSafe (path : String) : Bool := Id.run do
  if path.startsWith "/" then return false
  let components := path.splitOn "/"
  for c in components do
    if c == ".." then return false
  return true

/-- Create a tar archive from files, writing to output stream.
    `basePath` is stripped from file paths in the archive. -/
partial def create (output : IO.FS.Stream) (basePath : System.FilePath)
    (files : Array System.FilePath) : IO Unit := do
  let baseStr := basePath.toString
  -- Ensure baseStr ends with / to avoid matching /tmp/dir2 when base is /tmp/dir
  let basePfx := if baseStr.endsWith "/" then baseStr else baseStr ++ "/"
  for file in files do
    let fmeta ← file.metadata
    let fileStr := file.toString
    if fileStr == baseStr then continue
    let relPath :=
      if fileStr.startsWith basePfx then
        (fileStr.drop basePfx.length).toString
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
    -- Emit PAX extended header if needed (long path, large size, etc.)
    if let some paxData := needsPaxHeader entry then
      let paxBlock ← buildPaxEntry paxData entry.path
      output.write paxBlock
    -- Build UStar header, with truncated path if PAX is handling it
    let pathOvr : Option (String × String) :=
      if splitPath entry.path |>.isNone then
        -- PAX has the real path; use a truncated placeholder in UStar header
        some ("", String.fromUTF8! (entry.path.toUTF8.extract 0 (min entry.path.utf8ByteSize 100)))
      else none
    let header ← buildHeader entry pathOvr
    output.write header
    if !isDir then
      IO.FS.withFile file .read fun h => do
        let mut remaining := entry.size.toNat
        while remaining > 0 do
          let toRead := min remaining 65536
          let chunk ← h.read toRead.toUSize
          if chunk.isEmpty then
            throw (IO.userError s!"tar: file {relPath} shorter than expected ({remaining} bytes remaining)")
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

/-- Extract a tar archive from input stream to output directory.
    Handles UStar, GNU long name/link, and PAX extended headers. -/
partial def extract (input : IO.FS.Stream) (outDir : System.FilePath) : IO Unit := do
  let mut gnuLongName : Option String := none
  let mut gnuLongLink : Option String := none
  let mut paxOverrides : Option (Array (String × String)) := none
  repeat do
    let block ← input.read 512
    if block.size < 512 then break
    match ← parseHeader block with
    | none => break
    | some entry =>
      -- GNU long name: read data as the name for the next entry
      if entry.typeflag == typeGnuLongName then
        let nameData ← readEntryData input entry.size.toNat
        let name := String.fromUTF8! (nameData.extract 0 (Id.run do
          let mut n := nameData.size
          while n > 0 && nameData[n - 1]! == 0 do n := n - 1
          return n))
        gnuLongName := some name
        continue
      -- GNU long link: read data as the linkname for the next entry
      if entry.typeflag == typeGnuLongLink then
        let linkData ← readEntryData input entry.size.toNat
        let link := String.fromUTF8! (linkData.extract 0 (Id.run do
          let mut n := linkData.size
          while n > 0 && linkData[n - 1]! == 0 do n := n - 1
          return n))
        gnuLongLink := some link
        continue
      -- PAX extended header: parse records for the next entry
      if entry.typeflag == typePaxExtended then
        let paxData ← readEntryData input entry.size.toNat
        paxOverrides := some (parsePaxRecords paxData)
        continue
      -- PAX global header: skip (we don't track global state)
      if entry.typeflag == typePaxGlobal then
        let _ ← readEntryData input entry.size.toNat
        continue
      -- Apply GNU/PAX overrides
      let mut e := entry
      if let some name := gnuLongName then
        e := { e with path := name }
        gnuLongName := none
      if let some link := gnuLongLink then
        e := { e with linkname := link }
        gnuLongLink := none
      if let some records := paxOverrides then
        e := applyPaxOverrides e records
        paxOverrides := none
      -- Path safety: reject absolute paths and .. segments
      unless isPathSafe e.path do
        throw (IO.userError s!"tar: unsafe path: {e.path}")
      let outPath := outDir / e.path
      if e.typeflag == typeDirectory then
        IO.FS.createDirAll outPath
      else
        if let some parent := outPath.parent then
          IO.FS.createDirAll parent
        IO.FS.withFile outPath .write fun h => do
          let mut remaining := e.size.toNat
          while remaining > 0 do
            let toRead := min remaining 65536
            let chunk ← input.read toRead.toUSize
            if chunk.isEmpty then
              throw (IO.userError s!"tar: unexpected end of archive reading {e.path} ({remaining} bytes remaining)")
            h.write chunk
            remaining := remaining - chunk.size
        let pad := paddingFor e.size
        if pad > 0 then
          let _ ← input.read pad.toUSize

/-- List entries in a tar archive without extracting.
    Handles UStar, GNU long name/link, and PAX extended headers. -/
partial def list (input : IO.FS.Stream) : IO (Array Entry) := do
  let mut entries := #[]
  let mut gnuLongName : Option String := none
  let mut gnuLongLink : Option String := none
  let mut paxOverrides : Option (Array (String × String)) := none
  repeat do
    let block ← input.read 512
    if block.size < 512 then break
    match ← parseHeader block with
    | none => break
    | some entry =>
      -- GNU long name
      if entry.typeflag == typeGnuLongName then
        let nameData ← readEntryData input entry.size.toNat
        let name := String.fromUTF8! (nameData.extract 0 (Id.run do
          let mut n := nameData.size
          while n > 0 && nameData[n - 1]! == 0 do n := n - 1
          return n))
        gnuLongName := some name
        continue
      -- GNU long link
      if entry.typeflag == typeGnuLongLink then
        let linkData ← readEntryData input entry.size.toNat
        let link := String.fromUTF8! (linkData.extract 0 (Id.run do
          let mut n := linkData.size
          while n > 0 && linkData[n - 1]! == 0 do n := n - 1
          return n))
        gnuLongLink := some link
        continue
      -- PAX extended header
      if entry.typeflag == typePaxExtended then
        let paxData ← readEntryData input entry.size.toNat
        paxOverrides := some (parsePaxRecords paxData)
        continue
      -- PAX global header: skip
      if entry.typeflag == typePaxGlobal then
        let _ ← readEntryData input entry.size.toNat
        continue
      -- Apply GNU/PAX overrides
      let mut e := entry
      if let some name := gnuLongName then
        e := { e with path := name }
        gnuLongName := none
      if let some link := gnuLongLink then
        e := { e with linkname := link }
        gnuLongLink := none
      if let some records := paxOverrides then
        e := applyPaxOverrides e records
        paxOverrides := none
      entries := entries.push e
      -- Skip past file data + padding
      let dataSize := e.size.toNat + paddingFor e.size
      let mut skipped := 0
      while skipped < dataSize do
        let toRead := min (dataSize - skipped) 65536
        let chunk ← input.read toRead.toUSize
        if chunk.isEmpty then
          throw (IO.userError s!"tar: unexpected end of archive skipping {e.path}")
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
