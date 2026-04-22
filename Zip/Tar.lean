import ZipCommon.Binary
import Zip.Gzip
import ZipCommon.Handle
import Zip.Native.Gzip

/-! Tar archive creation, listing, and extraction with UStar, GNU, and PAX format support.
    Includes tar.gz compression/decompression via gzip integration. -/

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
/-- Typeflag for hard link. Recognised by name only — `extract` does not
    create hard links and silently skips entries with this typeflag. -/
def typeHardlink : UInt8 := 0x31  -- '1'
/-- Typeflag for directory. -/
def typeDirectory : UInt8 := 0x35  -- '5'
/-- Typeflag for symbolic link. -/
def typeSymlink : UInt8 := 0x32  -- '2'
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
  if h : offset < data.size then
    let firstByte := data[offset]
    -- GNU base-256: if high bit is set, remaining bytes are big-endian binary
    if firstByte &&& 0x80 != 0 then
      let mut result : UInt64 := (firstByte &&& 0x7F).toUInt64
      for hi : i in [1:len] do
        if h2 : offset + i < data.size then
          result := (result <<< 8) ||| data[offset + i].toUInt64
      return result
    -- Standard octal ASCII
    return Binary.readOctal data offset len
  else return 0

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
    let mut digitCount := 0
    while h : lenEnd < data.size do
      let b := data[lenEnd]
      if b == ' '.toNat.toUInt8 then
        lenEnd := lenEnd + 1
        break
      if b >= '0'.toNat.toUInt8 && b <= '9'.toNat.toUInt8 then
        digitCount := digitCount + 1
        if digitCount > 20 then  -- no legitimate PAX length exceeds 20 digits
          validLen := false
          break
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
      if h : eqPos < data.size then
        if data[eqPos] == '='.toNat.toUInt8 then break
      else break
      eqPos := eqPos + 1
    if eqPos < recordEnd then
      let keyBytes := data.extract lenEnd eqPos
      -- Value runs from after '=' to before trailing newline
      let valueEnd := if h : recordEnd - 1 < data.size then
                        if recordEnd > 0 && data[recordEnd - 1] == '\n'.toNat.toUInt8
                        then recordEnd - 1 else recordEnd
                      else recordEnd
      let valueBytes := data.extract (eqPos + 1) valueEnd
      -- Skip records with invalid UTF-8 rather than panicking
      if let (some key, some value) := (String.fromUTF8? keyBytes, String.fromUTF8? valueBytes) then
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

/-- Truncate `s` so that its UTF-8 byte length is at most `maxBytes`,
    stopping at a codepoint boundary. The result is always valid UTF-8,
    so callers can avoid the panicking fromUTF8 variant on the output.
    Used by the tar writer when placing a long path into a fixed-width
    header field (UStar name is 100 bytes, PAX placeholder is 80 bytes). -/
def truncateUTF8 (s : String) (maxBytes : Nat) : String :=
  if s.utf8ByteSize ≤ maxBytes then s
  else Id.run do
    let mut result := ""
    let mut bytes : Nat := 0
    for c in s.toList do
      let cBytes := c.utf8Size
      if bytes + cBytes > maxBytes then break
      result := result.push c
      bytes := bytes + cBytes
    return result

/-- Read exactly `n` bytes from a stream, looping on short reads.
    Returns fewer bytes only at true EOF. -/
private partial def readExact (input : IO.FS.Stream) (n : Nat) : IO ByteArray := do
  let mut buf := ByteArray.empty
  while buf.size < n do
    let remaining := n - buf.size
    let chunk ← input.read remaining.toUSize
    if chunk.isEmpty then return buf
    buf := buf ++ chunk
  return buf

/-- Default upper bound on a single GNU long-name / long-link / PAX
    header-entry payload accumulated by `readEntryData`. The four
    callers in `forEntries` buffer the entire payload into memory before
    treating it as a name, link target, or PAX record block, so an
    attacker-controlled `entry.size` from a crafted header would
    otherwise drive an arbitrarily large allocation.

    8 MiB was chosen as a safe default: GNU `PATH_MAX` is 4096 bytes on
    most systems, libarchive caps each PAX record block at roughly
    1 MiB, and 8 MiB still bounds the accumulator at three orders of
    magnitude above realistic header sizes. Callers that legitimately
    handle larger header blobs can raise the cap via the
    `maxHeaderSize` parameter exposed on `Tar.extract`, `Tar.list`,
    `Tar.extractTarGz`, and `Tar.extractTarGzNative`. -/
def defaultMaxHeaderSize : Nat := 8 * 1024 * 1024

/-- Read entry data from a stream (for GNU long name / PAX headers).
    `maxHeaderSize` caps the buffered payload before any allocation
    happens; on overflow the function throws `IO.userError` containing
    the substring `"exceeds maximum header size"`. The payload-bearing
    `Tar.extract` regular-file path uses its own open-coded loop and is
    not affected by this cap (see `Zip/Tar.lean` regular-file branch). -/
private partial def readEntryData (input : IO.FS.Stream) (size : Nat)
    (maxHeaderSize : Nat := defaultMaxHeaderSize) : IO ByteArray := do
  if size > maxHeaderSize then
    throw (IO.userError s!"tar: header entry size ({size}) exceeds maximum header size ({maxHeaderSize})")
  let mut result := ByteArray.empty
  let mut remaining := size
  while remaining > 0 do
    let toRead := min remaining 65536
    let chunk ← input.read toRead.toUSize
    if chunk.isEmpty then
      throw (IO.userError "tar: unexpected end of archive reading entry data")
    result := result ++ chunk
    remaining := remaining - chunk.size
  -- Skip padding (loop to handle short reads from pipes/fragmenting streams)
  let pad := paddingFor size.toUInt64
  if pad > 0 then
    let mut padRemaining := pad
    while padRemaining > 0 do
      let chunk ← input.read (min padRemaining 512).toUSize
      if chunk.isEmpty then
        throw (IO.userError "tar: unexpected end of archive reading padding")
      padRemaining := padRemaining - chunk.size
  return result

/-- Thin bounded-length `readExact`-style helper over `IO.FS.Stream`, adding the
    `length.toUSize.toNat = length` addressable-range guard that the ZIP
    `readExact` already applies at `Zip/Archive.lean` but the Tar `readExact`
    does not. On the addressable-range violation throws `IO.userError` with
    substring `"tar: {what} size {n} exceeds addressable range"`; on short read
    throws with the message produced by the caller-handled EOF path (the
    underlying loop returns a shorter `ByteArray` at true EOF — callers that
    require strict `length` bytes must check `result.size = length`).

    This wraps the existing private `readExact` for the Tar surface so callers
    on `Stream` get the same `Nat → USize` roundtrip as the ZIP `Handle` path.
    Cross-reference: `SECURITY_INVENTORY.md` § "Local guard inventory for
    `Handle.read` and `Stream.read`". -/
partial def readBoundedExactFromStream (s : IO.FS.Stream) (length : Nat)
    (what : String) : IO ByteArray := do
  unless length.toUSize.toNat == length do
    throw (IO.userError s!"tar: {what} size {length} exceeds addressable range")
  readExact s length

/-- General-purpose bounded wrapper around `readEntryData` that enforces a
    caller-supplied `maxSize` upper bound on the payload before the allocator
    loop starts. On violation throws `IO.userError` with substring
    `"exceeds maximum"` (stable phrase kept in sync with the existing
    `readEntryData` `"exceeds maximum header size"` guard). Otherwise delegates
    to `readEntryData` — the existing `maxHeaderSize` cap there still applies
    and uses the same substring anchor, so the two bounds compose.

    Used by callers that have a semantically meaningful per-call maximum
    (e.g. PAX record size, long-name size) distinct from `defaultMaxHeaderSize`.
    The existing `readEntryData (maxHeaderSize := ...)` signature is not a
    substitute for this helper: that parameter is the **global** default cap
    for any header-buffering caller, whereas `readBoundedEntryData` is the
    **per-call** cap primitive — typically the stricter of the two. Cross-
    reference: `SECURITY_INVENTORY.md` § "Local guard inventory for
    `Handle.read` and `Stream.read`". -/
partial def readBoundedEntryData (input : IO.FS.Stream) (size maxSize : Nat)
    (what : String) : IO ByteArray := do
  if size > maxSize then
    throw (IO.userError
      s!"tar: {what} size ({size}) exceeds maximum ({maxSize})")
  readEntryData input size

/-- Split a path into (prefix, name) for UStar format.
    Returns `none` if the path is too long to encode. -/
def splitPath (path : String) : Option (String × String) := Id.run do
  if path.utf8ByteSize <= 100 then
    return some ("", path)
  -- Find last '/' that gives name <= 100 and prefix <= 155
  let bytes := path.toUTF8
  let mut bestSplit : Option Nat := none
  for h : i in [:bytes.size] do
    if bytes[i] == '/'.toNat.toUInt8 then
      let nameLen := bytes.size - i - 1
      let pfxLen := i
      if nameLen <= 100 && pfxLen <= 155 then
        bestSplit := some i
  match bestSplit with
  | some i =>
    -- Safe: `i` is the index of a `'/'` byte (0x2F, ASCII), which is
    -- always a codepoint boundary. `bytes` comes from `path.toUTF8`,
    -- so both the prefix `[0, i)` and suffix `(i, size)` are valid
    -- UTF-8 by construction. No panic path through `fromUTF8!`.
    let pfx := String.fromUTF8! (bytes.extract 0 i)
    let name := String.fromUTF8! (bytes.extract (i + 1) bytes.size)
    return some (pfx, name)
  | none => return none

/-- Compute tar checksum: sum all 512 bytes, treating bytes 148..155 as spaces. -/
@[noinline] def computeChecksum (header : ByteArray) : UInt32 := Id.run do
  let mut sum : UInt32 := 0
  for h : i in [:header.size] do
    if i >= 512 then break
    if i >= 148 && i < 156 then
      sum := sum + ' '.toNat.toUInt32
    else
      sum := sum + header[i].toUInt32
  return sum

-- Helper to write fields into a header at a given offset
private def writeField := Binary.writeField

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
  -- Truncate the entry path to fit in UStar name field; `truncateUTF8`
  -- respects codepoint boundaries so multibyte paths never produce a
  -- partial UTF-8 sequence here.
  let paxName := s!"PaxHeader/{truncateUTF8 entryPath 80}"
  let paxEntry : Entry := {
    path := truncateUTF8 paxName 100
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
  if block.size < 512 then
    throw (IO.userError "tar: header block too short")
  -- We know block.size ≥ 512 after the guard
  -- Check for zero block (end of archive)
  let allZero := Id.run do
    let mut z := true
    for h : i in [:block.size] do
      if i >= 512 then break
      if block[i] != 0 then
        z := false
        break
    return z
  if allZero then return none
  -- Validate checksum
  unless verifyChecksum block do
    throw (IO.userError "tar: header checksum mismatch")
  -- Validate UStar magic (accept both "ustar\0" and "ustar " for compatibility)
  let magic := Binary.readString block hdrMagic.1 hdrMagic.2
  unless magic == "ustar" || magic == "ustar " do
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
    typeflag := if h : hdrTypeflag.1 < block.size then block[hdrTypeflag.1] else 0
    linkname := Binary.readString block hdrLinkname.1 hdrLinkname.2
    uname := Binary.readString block hdrUname.1 hdrUname.2
    gname := Binary.readString block hdrGname.1 hdrGname.2
  }

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
        -- PAX has the real path; use a truncated placeholder in UStar header.
        -- `truncateUTF8` keeps the placeholder valid UTF-8 even for paths
        -- whose 100th byte lands inside a multibyte sequence.
        some ("", truncateUTF8 entry.path 100)
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
  let sorted := files.qsort (·.toString < ·.toString)
  create output dir sorted

/-- Strip trailing NUL bytes from a byte array. -/
private def stripTrailingNuls (data : ByteArray) : ByteArray :=
  let n := Id.run do
    let mut n := data.size
    while n > 0 do
      if h : n - 1 < data.size then
        if data[n - 1] == 0 then n := n - 1 else break
      else break
    return n
  data.extract 0 n

/-- Skip past entry data and padding in the input stream. -/
private partial def skipEntryData (input : IO.FS.Stream) (size : UInt64) : IO Unit := do
  let dataSize := size.toNat + paddingFor size
  let mut skipped := 0
  while skipped < dataSize do
    let toRead := min (dataSize - skipped) 65536
    let chunk ← input.read toRead.toUSize
    if chunk.isEmpty then break
    skipped := skipped + chunk.size

/-- Iterate over entries in a tar archive stream, resolving GNU long name/link
    and PAX extended/global headers. Calls `f` for each resolved entry.
    The callback must consume `entry.size` bytes of data plus padding from
    the input stream (use `skipEntryData` to discard unwanted data).

    `maxHeaderSize` bounds the buffered payload of every GNU long-name,
    GNU long-link, PAX extended, and PAX global pseudo-entry; see
    `defaultMaxHeaderSize` for the rationale behind the default. The
    cap is independent of `Tar.extract`'s `maxEntrySize`, which only
    bounds payload-bearing entries. -/
private partial def forEntries (input : IO.FS.Stream)
    (f : Entry → IO Unit)
    (maxHeaderSize : Nat := defaultMaxHeaderSize) : IO Unit := do
  let mut gnuLongName : Option String := none
  let mut gnuLongLink : Option String := none
  let mut paxOverrides : Option (Array (String × String)) := none
  repeat do
    let block ← readExact input 512
    if block.size < 512 then break
    match ← parseHeader block with
    | none => break
    | some entry =>
      -- GNU long name: read data as the name for the next entry
      if entry.typeflag == typeGnuLongName then
        let nameData ← readBoundedEntryData input entry.size.toNat maxHeaderSize
          "GNU long name"
        let nameBytes := stripTrailingNuls nameData
        let name := match String.fromUTF8? nameBytes with
          | some s => s
          | none => Binary.fromLatin1 nameBytes
        gnuLongName := some name
        continue
      -- GNU long link: read data as the linkname for the next entry
      if entry.typeflag == typeGnuLongLink then
        let linkData ← readBoundedEntryData input entry.size.toNat maxHeaderSize
          "GNU long link"
        let linkBytes := stripTrailingNuls linkData
        let link := match String.fromUTF8? linkBytes with
          | some s => s
          | none => Binary.fromLatin1 linkBytes
        gnuLongLink := some link
        continue
      -- PAX extended header: parse records for the next entry
      if entry.typeflag == typePaxExtended then
        let paxData ← readBoundedEntryData input entry.size.toNat maxHeaderSize
          "PAX extended header"
        paxOverrides := some (parsePaxRecords paxData)
        continue
      -- PAX global header: skip (we don't track global state)
      if entry.typeflag == typePaxGlobal then
        let _ ← readBoundedEntryData input entry.size.toNat maxHeaderSize
          "PAX global header"
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
      f e

/-- Extract a tar archive from input stream to output directory.
    Handles UStar, GNU long name/link, and PAX extended headers.

    `maxEntrySize` bounds each entry's declared size — checked against the
    tar header's `e.size` before any payload bytes are read. Default `1 GiB`
    per entry; pass `0` to opt out into unlimited mode. Overflow raises
    `IO.userError` containing
    `"tar: entry '…' size (…) exceeds limit (…)"`.

    `maxTotalSize` (when non-zero) caps the sum of decompressed bytes across
    all entries written by this extraction. Default `0` means no whole-archive
    cap; rely on `maxEntrySize` for per-entry bounding. Overflow raises
    `IO.userError` containing
    `"tar: total extracted size (…) exceeds whole-archive limit (…)"`.
    See `SECURITY_INVENTORY.md` *Decompression Limit Inventory*.

    `maxHeaderSize` (default `defaultMaxHeaderSize` = 8 MiB) bounds the
    buffered payload of every GNU long-name, GNU long-link, and PAX
    pseudo-entry, independent of `maxEntrySize`. Overflow raises
    `IO.userError` containing the substring
    `"exceeds maximum header size"`.

    Per-typeflag policy:

    * `typeRegular` ('0'): write the payload to `outDir/path` after
      `Binary.isPathSafe` rejects unsafe paths.
    * `typeDirectory` ('5'): create `outDir/path` (and parents) after
      the same path-safety check.
    * `typeSymlink` ('2'): require `linkname` to be relative — reject
      any target that starts with `/`, contains `\`, or has any `..`
      component — then call `Handle.createSymlink`. The payload is
      always discarded.
    * Any other typeflag (including `typeHardlink` ('1') and device
      nodes): the payload is silently consumed and no filesystem entry
      is created. Hard links are never materialised; an attacker who
      crafts `typeflag == '1'` with a malicious `linkname` cannot
      escape `outDir`. -/
partial def extract (input : IO.FS.Stream) (outDir : System.FilePath)
    (maxEntrySize : UInt64 := 1024 * 1024 * 1024)
    (maxTotalSize : UInt64 := 0)
    (maxHeaderSize : Nat := defaultMaxHeaderSize) : IO Unit := do
  let totalRef ← IO.mkRef (0 : UInt64)
  forEntries (maxHeaderSize := maxHeaderSize) input fun e => do
    -- Strip trailing slash for path safety check (directories end with "/")
    let checkPath := if e.path.endsWith "/" then e.path.dropEnd 1 |>.toString else e.path
    unless Binary.isPathSafe checkPath do
      throw (IO.userError s!"tar: unsafe path: {e.path}")
    if maxEntrySize > 0 && e.size > maxEntrySize then
      throw (IO.userError s!"tar: entry '{e.path}' size ({e.size}) exceeds limit ({maxEntrySize})")
    let outPath := outDir / e.path
    -- Strip setuid/setgid/sticky, keep only rwxrwxrwx
    let mode := e.mode &&& 0o777
    if e.typeflag == typeDirectory then
      IO.FS.createDirAll outPath
      if mode != 0 then
        IO.Prim.setAccessRights outPath mode
      skipEntryData input e.size
    else if e.typeflag == typeRegular then
      -- Whole-archive running-total check: fires before any payload bytes are
      -- written for this entry. Only regular-file payloads contribute.
      if maxTotalSize > 0 then
        let running ← totalRef.get
        if maxTotalSize - running < e.size then
          throw (IO.userError s!"tar: total extracted size ({e.size.toNat + running.toNat}) exceeds whole-archive limit ({maxTotalSize})")
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
      if mode != 0 then
        IO.Prim.setAccessRights outPath mode
      let pad := paddingFor e.size
      if pad > 0 then
        let mut padRemaining := pad
        while padRemaining > 0 do
          let chunk ← input.read (min padRemaining 512).toUSize
          if chunk.isEmpty then break
          padRemaining := padRemaining - chunk.size
      totalRef.modify (· + e.size)
    else if e.typeflag == typeSymlink then
      -- Component-level validation: reject absolute, backslash, and `..` traversal
      if e.linkname.startsWith "/" || e.linkname.any (· == '\\') then
        throw (IO.userError s!"tar: unsafe symlink target: {e.linkname}")
      if e.linkname.splitOn "/" |>.any (· == "..") then
        throw (IO.userError s!"tar: unsafe symlink target: {e.linkname}")
      if let some parent := outPath.parent then
        IO.FS.createDirAll parent
      Handle.createSymlink e.linkname outPath.toString
      skipEntryData input e.size
    else
      -- Skip unsupported entry types: `typeHardlink` ('1'), character
      -- and block devices, FIFOs, GNU sparse, etc. The payload is
      -- discarded and no filesystem entry is created — hard links
      -- specifically are never materialised so a crafted `linkname`
      -- cannot escape `outDir`.
      skipEntryData input e.size

/-- List entries in a tar archive without extracting.
    Handles UStar, GNU long name/link, and PAX extended headers.

    `maxHeaderSize` (default `defaultMaxHeaderSize` = 8 MiB) bounds the
    buffered payload of every GNU long-name, GNU long-link, and PAX
    pseudo-entry. Overflow raises `IO.userError` containing the
    substring `"exceeds maximum header size"`. -/
partial def list (input : IO.FS.Stream)
    (maxHeaderSize : Nat := defaultMaxHeaderSize) : IO (Array Entry) := do
  let entriesRef ← IO.mkRef (#[] : Array Entry)
  forEntries (maxHeaderSize := maxHeaderSize) input fun e => do
    entriesRef.modify (·.push e)
    skipEntryData input e.size
  entriesRef.get

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
    True streaming — bounded memory regardless of archive size.

    `maxEntrySize` bounds each entry's declared size before any payload
    bytes are read. Default `1 GiB` per entry; pass `0` to opt out into
    unlimited mode. Overflow raises `IO.userError` containing
    `"tar: entry '…' size (…) exceeds limit (…)"`. There is no
    outer gzip-stream cap on this variant: streaming FFI gzip has no
    `maxOutputSize` parameter today (the known gap tracked by
    `SECURITY_INVENTORY.md` *Decompression Limit Inventory*, recommendation 2).

    `maxTotalSize` (when non-zero) caps the sum of decompressed bytes across
    all entries written by this extraction. Default `0` means no whole-archive
    cap; rely on `maxEntrySize` for per-entry bounding. Overflow raises
    `IO.userError` containing
    `"tar: total extracted size (…) exceeds whole-archive limit (…)"`.
    See `SECURITY_INVENTORY.md` *Decompression Limit Inventory*.

    `maxHeaderSize` (default `defaultMaxHeaderSize` = 8 MiB) bounds the
    buffered payload of every GNU long-name, GNU long-link, and PAX
    pseudo-entry. Overflow raises `IO.userError` containing the
    substring `"exceeds maximum header size"`. -/
partial def extractTarGz (inputPath : System.FilePath) (outDir : System.FilePath)
    (maxEntrySize : UInt64 := 1024 * 1024 * 1024)
    (maxTotalSize : UInt64 := 0)
    (maxHeaderSize : Nat := defaultMaxHeaderSize) : IO Unit := do
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
    extract tarStream outDir maxEntrySize maxTotalSize maxHeaderSize

/-- Extract a .tar.gz archive using pure Lean decompression (no C FFI).
    Unlike `extractTarGz`, this reads the entire file into memory before
    decompressing, so memory usage is O(file_size). Use this when C
    libraries are unavailable.

    `maxEntrySize` bounds each entry's declared size before any payload
    bytes are read. Default `1 GiB` per entry; pass `0` to opt out into
    unlimited mode. Overflow raises `IO.userError`
    containing `"tar: entry '…' size (…) exceeds limit (…)"`.

    `maxTotalSize` (when non-zero) caps the sum of decompressed bytes across
    all entries written by this extraction. Default `0` means no whole-archive
    cap; rely on `maxEntrySize` for per-entry bounding. Overflow raises
    `IO.userError` containing
    `"tar: total extracted size (…) exceeds whole-archive limit (…)"`.
    See `SECURITY_INVENTORY.md` *Decompression Limit Inventory*.

    `maxOutputSize` (default 256 MiB) caps the decompressed tar buffer
    produced by the outer native gzip decode. Unlike the FFI path, where
    `0` means unlimited, here `0` rejects any non-empty output (the
    underlying native `GzipDecode.decompress` compares
    `output.size + len > maxOutputSize`, so even a single produced byte
    exceeds the bound). Overflow raises `IO.userError` containing
    `"exceeds maximum size"`, wrapped as
    `"tar.gz: native gzip decompression failed: …"`.
    The native variant exposes this parameter because the pure Lean
    `Zip.Native.GzipDecode.decompress` API requires a bound up front;
    the streaming `extractTarGz` variant does not need one because it
    drains the outer compressed stream chunk-by-chunk into the tar
    parser.
    See `SECURITY_INVENTORY.md` *Decompression Limit Inventory*.

    `maxHeaderSize` (default `defaultMaxHeaderSize` = 8 MiB) bounds the
    buffered payload of every GNU long-name, GNU long-link, and PAX
    pseudo-entry. Overflow raises `IO.userError` containing the
    substring `"exceeds maximum header size"`. -/
partial def extractTarGzNative (inputPath : System.FilePath) (outDir : System.FilePath)
    (maxEntrySize : UInt64 := 1024 * 1024 * 1024)
    (maxTotalSize : UInt64 := 0)
    (maxOutputSize : Nat := 256 * 1024 * 1024)
    (maxHeaderSize : Nat := defaultMaxHeaderSize) : IO Unit := do
  let gzData ← IO.FS.readBinFile inputPath
  let tarData ← match Zip.Native.GzipDecode.decompress gzData maxOutputSize with
    | .ok data => pure data
    | .error msg => throw (IO.userError s!"tar.gz: native gzip decompression failed: {msg}")
  -- Create a ByteArray-backed read stream
  let posRef ← IO.mkRef (0 : Nat)
  let tarStream : IO.FS.Stream := {
    flush := pure ()
    read := fun n => do
      let pos ← posRef.get
      let avail := tarData.size - pos
      if avail == 0 then return .empty
      let toRead := min avail n.toNat
      let result := tarData.extract pos (pos + toRead)
      posRef.set (pos + toRead)
      return result
    write := fun _ => pure ()
    getLine := pure ""
    putStr := fun _ => pure ()
    isTty := pure false
  }
  extract tarStream outDir maxEntrySize maxTotalSize maxHeaderSize

end Tar
