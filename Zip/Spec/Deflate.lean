import Zip.Spec.Huffman

/-!
# DEFLATE Bitstream Specification (RFC 1951)

Formal specification of the DEFLATE compressed data format. This defines
what constitutes a valid DEFLATE bitstream and what output it produces,
independently of any particular decompressor implementation.

The specification is structured in layers:
1. **Bitstream**: bytes to bits conversion (LSB-first per byte)
2. **LZ77 symbols**: the decoded symbol alphabet (literals, references, end)
3. **Block structure**: stored, fixed Huffman, and dynamic Huffman blocks
4. **Stream decode**: sequence of blocks terminated by a final block

The key correctness theorem (to be proved in future sessions) is that the
`Zip.Native.Inflate.inflate` implementation agrees with this specification.
-/

namespace Deflate.Spec

/-! ## Bitstream conversion -/

/-- Convert a `ByteArray` to a list of bits, LSB first per byte.
    This matches the DEFLATE bit packing order (RFC 1951 §3.1.1).
    Uses `data.data.toList` (not `data.toList`) because the latter uses
    an `@[irreducible]` loop that's hard to reason about. -/
def bytesToBits (data : ByteArray) : List Bool :=
  data.data.toList.flatMap byteToBits
where
  byteToBits (b : UInt8) : List Bool :=
    List.ofFn fun (i : Fin 8) => b.toNat.testBit i.val

/-- Read `n` bits from a bit stream as a natural number (LSB first).
    Returns the value and remaining bits, or `none` if not enough bits. -/
def readBitsLSB : Nat → List Bool → Option (Nat × List Bool)
  | 0, bits => some (0, bits)
  | _ + 1, [] => none
  | n + 1, b :: rest => do
    let (val, remaining) ← readBitsLSB n rest
    return ((if b then 1 else 0) + val * 2, remaining)

/-- Read `n` bits from a bit stream as a natural number (MSB first).
    Not currently used; kept as spec infrastructure for potential
    future proof needs (e.g. connecting MSB Huffman codes to bitstreams). -/
def readBitsMSB : Nat → List Bool → Option (Nat × List Bool)
  | 0, bits => some (0, bits)
  | _ + 1, [] => none
  | n + 1, b :: rest => do
    let (val, remaining) ← readBitsMSB n rest
    return (val + (if b then 1 else 0) * 2^n, remaining)

/-- Skip to the next byte boundary (discard remaining bits in the
    current byte). Works because `bytesToBits` always produces a
    multiple-of-8 list, so `bits.length % 8` gives the padding needed. -/
def alignToByte (bits : List Bool) : List Bool :=
  bits.drop (bits.length % 8)

/-! ## Bitstream theorems -/

/-- Each byte converts to exactly 8 bits. -/
private theorem byteToBits_length (b : UInt8) :
    (bytesToBits.byteToBits b).length = 8 := by
  simp [bytesToBits.byteToBits]

/-- `bytesToBits` produces exactly `data.size * 8` bits. -/
theorem bytesToBits_length (data : ByteArray) :
    (bytesToBits data).length = data.size * 8 := by
  simp only [bytesToBits, ByteArray.size]
  suffices ∀ l : List UInt8,
      (l.flatMap bytesToBits.byteToBits).length = l.length * 8 by
    rw [this, Array.length_toList]
  intro l; induction l with
  | nil => simp
  | cons b bs ih =>
    simp only [List.flatMap_cons, List.length_append, List.length_cons,
               byteToBits_length, ih]; omega

/-- `readBitsLSB` consumes exactly `n` bits when it succeeds. -/
theorem readBitsLSB_some_length {n : Nat} {bits : List Bool}
    {val : Nat} {rest : List Bool}
    (h : readBitsLSB n bits = some (val, rest)) :
    rest.length + n = bits.length := by
  induction n generalizing bits val with
  | zero =>
    unfold readBitsLSB at h; simp at h; obtain ⟨-, rfl⟩ := h; simp
  | succ k ih =>
    cases bits with
    | nil => simp [readBitsLSB] at h
    | cons b bs =>
      simp only [readBitsLSB] at h
      cases hk : readBitsLSB k bs with
      | none => simp [hk] at h
      | some p =>
        obtain ⟨v, rem⟩ := p
        simp [hk] at h
        obtain ⟨-, rfl⟩ := h
        have := ih hk; simp only [List.length_cons]; omega

/-! ## LZ77 symbol alphabet -/

/-- The symbols produced by DEFLATE Huffman decoding, before LZ77
    back-reference resolution. -/
inductive LZ77Symbol where
  /-- A literal byte (codes 0–255). -/
  | literal (byte : UInt8)
  /-- A length-distance back-reference (length codes 257–285 + distance). -/
  | reference (length : Nat) (distance : Nat)
  /-- End of block marker (code 256). -/
  | endOfBlock
  deriving Repr, BEq

/-- Resolve a sequence of LZ77 symbols to produce output bytes.
    Returns `none` if any back-reference is invalid (distance exceeds
    current output size). -/
def resolveLZ77 : List LZ77Symbol → List UInt8 → Option (List UInt8)
  | [], acc => some acc
  | .literal b :: rest, acc => resolveLZ77 rest (acc ++ [b])
  | .endOfBlock :: _, acc => some acc
  | .reference len dist :: rest, acc =>
    if dist == 0 || dist > acc.length then none
    else
      let start := acc.length - dist
      let copied := List.ofFn fun (i : Fin len) =>
        acc[start + (i.val % dist)]!
      resolveLZ77 rest (acc ++ copied)

/-! ## resolveLZ77 properties -/

/-- Empty symbol list returns the accumulator unchanged. -/
@[simp] theorem resolveLZ77_nil (acc : List UInt8) :
    resolveLZ77 [] acc = some acc := rfl

/-- End-of-block marker returns the accumulator, ignoring remaining symbols. -/
@[simp] theorem resolveLZ77_endOfBlock (rest : List LZ77Symbol) (acc : List UInt8) :
    resolveLZ77 (.endOfBlock :: rest) acc = some acc := rfl

/-- A literal symbol appends the byte and continues resolving. -/
@[simp] theorem resolveLZ77_literal (b : UInt8) (rest : List LZ77Symbol) (acc : List UInt8) :
    resolveLZ77 (.literal b :: rest) acc = resolveLZ77 rest (acc ++ [b]) := rfl

/-- A reference with distance 0 fails. -/
theorem resolveLZ77_reference_dist_zero (len : Nat) (rest : List LZ77Symbol)
    (acc : List UInt8) :
    resolveLZ77 (.reference len 0 :: rest) acc = none := by
  simp [resolveLZ77]

/-- A reference with distance exceeding the accumulator length fails. -/
theorem resolveLZ77_reference_dist_too_large (len dist : Nat)
    (rest : List LZ77Symbol) (acc : List UInt8)
    (h : dist > acc.length) :
    resolveLZ77 (.reference len dist :: rest) acc = none := by
  simp [resolveLZ77]
  intro hd
  omega

/-- A sequence of literal symbols resolves to the accumulator followed
    by those bytes. -/
theorem resolveLZ77_literals (bytes : List UInt8) (acc : List UInt8) :
    resolveLZ77 (bytes.map .literal ++ [.endOfBlock]) acc =
      some (acc ++ bytes) := by
  induction bytes generalizing acc with
  | nil => simp
  | cons b bs ih =>
    simp only [List.map_cons, List.cons_append, resolveLZ77_literal]
    rw [ih]; congr 1; simp [List.append_assoc]

/-- `resolveLZ77` with only literals (no endOfBlock) continues processing.
    If the remaining symbols resolve, so does the whole list. -/
theorem resolveLZ77_literal_cons (b : UInt8) (rest : List LZ77Symbol)
    (acc output : List UInt8) :
    resolveLZ77 (.literal b :: rest) acc = some output ↔
    resolveLZ77 rest (acc ++ [b]) = some output := by
  simp [resolveLZ77]

/-- `resolveLZ77` starting from empty accumulator with just an endOfBlock
    returns the empty list. -/
theorem resolveLZ77_endOfBlock_empty :
    resolveLZ77 [.endOfBlock] [] = some [] := rfl

/-- A valid back-reference unfolds to copying and continuing resolution. -/
theorem resolveLZ77_reference_valid (len dist : Nat) (rest : List LZ77Symbol)
    (acc : List UInt8) (hd : dist ≠ 0) (hdist : dist ≤ acc.length) :
    resolveLZ77 (.reference len dist :: rest) acc =
      let start := acc.length - dist
      let copied := List.ofFn fun (i : Fin len) =>
        acc[start + (i.val % dist)]!
      resolveLZ77 rest (acc ++ copied) := by
  have h1 : ¬(dist = 0) := hd
  have h2 : ¬(acc.length < dist) := by omega
  simp [resolveLZ77, h1, h2]

/-- If `resolveLZ77` succeeds, the output extends the initial accumulator. -/
theorem resolveLZ77_extends (syms : List LZ77Symbol) (acc output : List UInt8)
    (h : resolveLZ77 syms acc = some output) :
    acc <+: output := by
  induction syms generalizing acc with
  | nil => simp [resolveLZ77] at h; exact h ▸ List.prefix_refl _
  | cons sym rest ih =>
    cases sym with
    | literal b =>
      simp [resolveLZ77] at h
      have := ih _ h
      exact List.IsPrefix.trans (List.prefix_append _ _) this
    | endOfBlock =>
      simp [resolveLZ77] at h; exact h ▸ List.prefix_refl _
    | reference len dist =>
      simp only [resolveLZ77] at h
      split at h
      · contradiction
      · have := ih _ h
        exact List.IsPrefix.trans (List.prefix_append _ _) this

/-! ## DEFLATE tables (RFC 1951 §3.2.5) -/

/-- Length base values for literal/length codes 257–285. -/
def lengthBase : Array Nat := #[
  3, 4, 5, 6, 7, 8, 9, 10, 11, 13, 15, 17, 19, 23, 27, 31,
  35, 43, 51, 59, 67, 83, 99, 115, 131, 163, 195, 227, 258
]

/-- Extra bits for length codes 257–285. -/
def lengthExtra : Array Nat := #[
  0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 2, 2, 2, 2,
  3, 3, 3, 3, 4, 4, 4, 4, 5, 5, 5, 5, 0
]

/-- Distance base values for distance codes 0–29. -/
def distBase : Array Nat := #[
  1, 2, 3, 4, 5, 7, 9, 13, 17, 25, 33, 49, 65, 97, 129, 193,
  257, 385, 513, 769, 1025, 1537, 2049, 3073, 4097, 6145, 8193, 12289,
  16385, 24577
]

/-- Extra bits for distance codes 0–29. -/
def distExtra : Array Nat := #[
  0, 0, 0, 0, 1, 1, 2, 2, 3, 3, 4, 4, 5, 5, 6, 6,
  7, 7, 8, 8, 9, 9, 10, 10, 11, 11, 12, 12, 13, 13
]

/-- Fixed literal/length code lengths (RFC 1951 §3.2.6). -/
def fixedLitLengths : List Nat :=
  List.replicate 144 8 ++ List.replicate 112 9 ++
  List.replicate 24 7 ++ List.replicate 8 8

/-- Fixed distance code lengths (RFC 1951 §3.2.6). -/
def fixedDistLengths : List Nat := List.replicate 32 5

/-- Code length alphabet order for dynamic Huffman (RFC 1951 §3.2.7). -/
def codeLengthOrder : Array Nat := #[
  16, 17, 18, 0, 8, 7, 9, 6, 10, 5, 11, 4, 12, 3, 13, 2, 14, 1, 15
]

/-! ## Block decoding -/

/-- Decode one literal/length symbol from the bitstream.
    Returns the LZ77 symbol and remaining bits. -/
def decodeLitLen (litLengths : List Nat) (distLengths : List Nat)
    (bits : List Bool) : Option (LZ77Symbol × List Bool) := do
  -- Decode literal/length symbol using Huffman code
  let litCodes := Huffman.Spec.allCodes litLengths
  let litTable := litCodes.map fun (sym, cw) => (cw, sym)
  let (sym, bits) ← Huffman.Spec.decode litTable bits
  if sym < 256 then
    return (.literal sym.toUInt8, bits)
  else if sym == 256 then
    return (.endOfBlock, bits)
  else
    -- Length code 257–285
    let idx := sym - 257
    let base ← lengthBase[idx]?
    let extra ← lengthExtra[idx]?
    let (extraVal, bits) ← readBitsLSB extra bits
    let length := base + extraVal
    -- Distance code
    let distCodes := Huffman.Spec.allCodes distLengths
    let distTable := distCodes.map fun (s, cw) => (cw, s)
    let (dSym, bits) ← Huffman.Spec.decode distTable bits
    let dBase ← distBase[dSym]?
    let dExtra ← distExtra[dSym]?
    let (dExtraVal, bits) ← readBitsLSB dExtra bits
    let distance := dBase + dExtraVal
    return (.reference length distance, bits)

/-- Decode a sequence of LZ77 symbols from a Huffman-coded block.
    Decodes until end-of-block marker (code 256) is found.
    Uses fuel to ensure termination. -/
def decodeSymbols (litLengths distLengths : List Nat) (bits : List Bool)
    (fuel : Nat := 10000000) : Option (List LZ77Symbol × List Bool) :=
  match fuel with
  | 0 => none
  | fuel + 1 => do
    let (sym, bits) ← decodeLitLen litLengths distLengths bits
    match sym with
    | .endOfBlock => return ([.endOfBlock], bits)
    | _ =>
      let (rest, bits) ← decodeSymbols litLengths distLengths bits fuel
      return (sym :: rest, bits)

/-- Decode a stored (uncompressed) block.
    Reads LEN and NLEN, verifies the complement check,
    and returns the raw bytes. -/
def decodeStored (bits : List Bool) :
    Option (List UInt8 × List Bool) := do
  -- Align to byte boundary
  let bits := alignToByte bits
  -- Read LEN (16 bits, little-endian) and NLEN (16 bits, little-endian)
  let (len, bits) ← readBitsLSB 16 bits
  let (nlen, bits) ← readBitsLSB 16 bits
  -- Verify complement
  guard (len ^^^ nlen == 0xFFFF)
  -- Read `len` bytes (each is 8 bits)
  readNBytes len bits []
where
  readNBytes : Nat → List Bool → List UInt8 →
      Option (List UInt8 × List Bool)
    | 0, bits, acc => some (acc, bits)
    | n + 1, bits, acc => do
      let (val, bits) ← readBitsLSB 8 bits
      readNBytes n bits (acc ++ [val.toUInt8])

/-- Read code length code lengths from the bitstream. -/
private def readCLLengths : Nat → Nat → List Nat → List Bool →
    Option (List Nat × List Bool)
  | 0, _, acc, bits => some (acc, bits)
  | n + 1, idx, acc, bits => do
    let (val, bits) ← readBitsLSB 3 bits
    let pos := codeLengthOrder[idx]!
    let acc := acc.set pos val
    readCLLengths n (idx + 1) acc bits

/-- Decode dynamic Huffman code lengths from the bitstream
    (RFC 1951 §3.2.7). Returns literal/length and distance code lengths. -/
def decodeDynamicTables (bits : List Bool) :
    Option (List Nat × List Nat × List Bool) := do
  let (hlit, bits) ← readBitsLSB 5 bits
  let (hdist, bits) ← readBitsLSB 5 bits
  let (hclen, bits) ← readBitsLSB 4 bits
  let numLitLen := hlit + 257
  let numDist := hdist + 1
  let numCodeLen := hclen + 4
  -- Read code length code lengths
  let (clLengths, bits) ← readCLLengths numCodeLen 0
    (List.replicate 19 0) bits
  -- Decode the literal/length + distance lengths using the CL Huffman code
  let totalCodes := numLitLen + numDist
  let clCodes := Huffman.Spec.allCodes clLengths 7
  let clTable := clCodes.map fun (sym, cw) => (cw, sym)
  let (codeLengths, bits) ← decodeCLSymbols clTable totalCodes [] bits totalCodes
  guard (codeLengths.length == totalCodes)
  let litLenLengths := codeLengths.take numLitLen
  let distLengths := codeLengths.drop numLitLen
  return (litLenLengths, distLengths, bits)
where
  decodeCLSymbols (clTable : List (Huffman.Spec.Codeword × Nat))
      (totalCodes : Nat) (acc : List Nat) (bits : List Bool) :
      Nat → Option (List Nat × List Bool)
    | 0 => none
    | fuel + 1 => do
      if acc.length ≥ totalCodes then return (acc, bits)
      let (sym, bits) ← Huffman.Spec.decode clTable bits
      if sym < 16 then
        decodeCLSymbols clTable totalCodes (acc ++ [sym]) bits fuel
      else if sym == 16 then
        guard (acc.length > 0)
        let (rep, bits) ← readBitsLSB 2 bits
        let prev := acc.getLast!
        let acc := acc ++ List.replicate (rep + 3) prev
        guard (acc.length ≤ totalCodes)
        decodeCLSymbols clTable totalCodes acc bits fuel
      else if sym == 17 then
        let (rep, bits) ← readBitsLSB 3 bits
        let acc := acc ++ List.replicate (rep + 3) 0
        guard (acc.length ≤ totalCodes)
        decodeCLSymbols clTable totalCodes acc bits fuel
      else if sym == 18 then
        let (rep, bits) ← readBitsLSB 7 bits
        let acc := acc ++ List.replicate (rep + 11) 0
        guard (acc.length ≤ totalCodes)
        decodeCLSymbols clTable totalCodes acc bits fuel
      else none

/-! ## Stream decode -/

/-- A decoded DEFLATE block: its type and the output bytes it produces. -/
structure DecodedBlock where
  isFinal : Bool
  bytes : List UInt8

/-- Decode one DEFLATE block from the bitstream.
    Returns the decoded block and remaining bits. -/
def decodeBlock (bits : List Bool) :
    Option (DecodedBlock × List Bool) := do
  let (bfinal, bits) ← readBitsLSB 1 bits
  let (btype, bits) ← readBitsLSB 2 bits
  match btype with
  | 0 => -- Stored block
    let (bytes, bits) ← decodeStored bits
    return (⟨bfinal == 1, bytes⟩, bits)
  | 1 => -- Fixed Huffman
    let (syms, bits) ← decodeSymbols fixedLitLengths fixedDistLengths bits
    let output ← resolveLZ77 syms []
    return (⟨bfinal == 1, output⟩, bits)
  | 2 => -- Dynamic Huffman
    let (litLens, distLens, bits) ← decodeDynamicTables bits
    let (syms, bits) ← decodeSymbols litLens distLens bits
    let output ← resolveLZ77 syms []
    return (⟨bfinal == 1, output⟩, bits)
  | _ => none  -- reserved block type (3)

/-- Decode a complete DEFLATE stream: a sequence of blocks ending
    with a final block. Returns the concatenated output.
    Uses fuel to ensure termination. -/
def decode (bits : List Bool) (fuel : Nat := 10001) :
    Option (List UInt8) :=
  go bits [] fuel
where
  go (bits : List Bool) (acc : List UInt8) :
      Nat → Option (List UInt8)
    | 0 => none
    | fuel + 1 => do
      let (block, bits) ← decodeBlock bits
      let acc := acc ++ block.bytes
      if block.isFinal then return acc
      else go bits acc fuel

/-- Decode a DEFLATE stream from a `ByteArray` starting at a given byte
    offset. This is the top-level spec function. -/
def decodeBytes (data : ByteArray) (startPos : Nat := 0) :
    Option (List UInt8) :=
  let allBits := bytesToBits data
  let bits := allBits.drop (startPos * 8)
  decode bits

/-! ## Correctness theorems (to be proved) -/

/-- The spec decode function is deterministic: given the same input,
    it always produces the same output. (This is trivially true for a
    pure function, but stated for clarity.) -/
theorem decode_deterministic (bits : List Bool) (fuel : Nat) :
    ∀ a b, decode bits fuel = some a → decode bits fuel = some b → a = b := by
  intro a b h₁ h₂; simp_all

/-- Fixed literal/length code lengths have the correct size (288 symbols). -/
theorem fixedLitLengths_length : fixedLitLengths.length = 288 := by
  simp only [fixedLitLengths, List.length_append, List.length_replicate]

/-- Fixed distance code lengths have the correct size (32 symbols). -/
theorem fixedDistLengths_length : fixedDistLengths.length = 32 := by
  simp only [fixedDistLengths, List.length_replicate]

set_option maxRecDepth 2048 in
/-- Fixed literal/length code lengths form a valid Huffman code. -/
theorem fixedLitLengths_valid : Huffman.Spec.ValidLengths fixedLitLengths 15 := by
  constructor
  · intro l hl
    simp only [fixedLitLengths, List.mem_append, List.mem_replicate] at hl
    omega
  · decide

/-- Fixed distance code lengths form a valid Huffman code.
    Uses maxBits = 15 to match the default in `codeFor`/`allCodes`. -/
theorem fixedDistLengths_valid : Huffman.Spec.ValidLengths fixedDistLengths 15 := by
  constructor
  · intro l hl
    simp only [fixedDistLengths, List.mem_replicate] at hl
    omega
  · decide

/-- The fixed literal/length Huffman codes are prefix-free. -/
theorem fixedLitCodes_prefix_free :
    Huffman.Spec.IsPrefixFree
      ((Huffman.Spec.allCodes fixedLitLengths 15).map Prod.snd) :=
  Huffman.Spec.allCodeWords_prefix_free fixedLitLengths 15 fixedLitLengths_valid

/-- The fixed distance Huffman codes are prefix-free. -/
theorem fixedDistCodes_prefix_free :
    Huffman.Spec.IsPrefixFree
      ((Huffman.Spec.allCodes fixedDistLengths 15).map Prod.snd) :=
  Huffman.Spec.allCodeWords_prefix_free fixedDistLengths 15 fixedDistLengths_valid

end Deflate.Spec
