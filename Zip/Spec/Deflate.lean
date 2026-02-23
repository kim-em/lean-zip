import Zip.Spec.Huffman
import Zip.Spec.LZ77

/-!
# DEFLATE Bitstream Specification (RFC 1951)

Formal specification of the DEFLATE compressed data format. This defines
what constitutes a valid DEFLATE bitstream and what output it produces,
independently of any particular decompressor implementation.

The specification is structured in layers:
1. **Bitstream**: bytes to bits conversion (LSB-first per byte)
2. **LZ77 symbols**: see `Zip.Spec.LZ77`
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

/-- Skip to the next byte boundary (discard remaining bits in the
    current byte). Works because `bytesToBits` always produces a
    multiple-of-8 list, so `bits.length % 8` gives the padding needed. -/
def alignToByte (bits : List Bool) : List Bool :=
  bits.drop (bits.length % 8)

/-! ## Bitstream theorems -/

/-- Each byte converts to exactly 8 bits. -/
protected theorem bytesToBits.byteToBits_length (b : UInt8) :
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
               bytesToBits.byteToBits_length, ih]; omega

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

/-- `readBitsLSB n` produces values strictly less than `2^n`. -/
theorem readBitsLSB_bound {n : Nat} {bits : List Bool}
    {val : Nat} {rest : List Bool}
    (h : readBitsLSB n bits = some (val, rest)) :
    val < 2 ^ n := by
  induction n generalizing bits val with
  | zero => simp [readBitsLSB] at h; omega
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
        obtain ⟨rfl, rfl⟩ := h
        have := ih hk; split <;> omega

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

/-! ## Bitstream packing (inverse of `bytesToBits`) -/

/-- Convert a list of bits (LSB first) to a Nat value.
    Takes at most `n` bits. -/
def bitsToNat : Nat → List Bool → Nat
  | 0, _ => 0
  | _, [] => 0
  | n + 1, b :: rest => (if b then 1 else 0) + 2 * bitsToNat n rest

/-- Convert up to 8 bits (LSB first) to a byte value.
    Pads with `false` (0) if fewer than 8 bits are provided. -/
def bitsToByte (bits : List Bool) : UInt8 :=
  (bitsToNat 8 bits).toUInt8

/-- Pack a list of bits into a ByteArray, LSB first per byte.
    Pads the last byte with zero bits if needed. -/
def bitsToBytes (bits : List Bool) : ByteArray :=
  go bits ByteArray.empty
where
  go : List Bool → ByteArray → ByteArray
    | [], acc => acc
    | b :: rest, acc =>
      let byte := bitsToByte (b :: rest)
      go ((b :: rest).drop 8) (acc.push byte)
  termination_by bits => bits.length
  decreasing_by simp [List.length_drop]; omega

/-- Write a natural number as `n` bits LSB-first. -/
def writeBitsLSB : Nat → Nat → List Bool
  | 0, _ => []
  | n + 1, val => (val % 2 == 1) :: writeBitsLSB n (val / 2)

/-! ## Stored block encoding -/

/-- Convert a byte to 8 bits (LSB first), matching `bytesToBits.byteToBits`. -/
private def byteToBitsSpec (b : UInt8) : List Bool :=
  List.ofFn fun (i : Fin 8) => b.toNat.testBit i.val

/-- Encode a 16-bit value as 16 bits in LSB-first order. -/
private def encodeLEU16 (v : Nat) : List Bool :=
  let lo := v % 256
  let hi := v / 256
  byteToBitsSpec lo.toUInt8 ++ byteToBitsSpec hi.toUInt8

/-- Encode one stored block (data must be at most 65535 bytes).
    Does NOT include BFINAL/BTYPE bits (those are emitted by the caller). -/
private def encodeStoredBlock (data : List UInt8) : List Bool :=
  let len := data.length
  let nlen := len ^^^ 0xFFFF
  encodeLEU16 len ++ encodeLEU16 nlen ++ data.flatMap byteToBitsSpec

/-- Encode data as a sequence of stored DEFLATE blocks (spec level).
    Produces the complete bit-list representation including BFINAL/BTYPE
    for each block. Splits data into blocks of at most 65535 bytes. -/
def encodeStored (data : List UInt8) : List Bool :=
  if data.length ≤ 65535 then
    -- Single final block
    [true, false, false] ++ encodeStoredBlock data
  else
    -- Non-final block with 65535 bytes, then recurse
    let block := data.take 65535
    let rest := data.drop 65535
    [false, false, false] ++ encodeStoredBlock block ++ encodeStored rest
termination_by data.length
decreasing_by
  simp only [List.length_drop]
  omega

/-- Read code length code lengths from the bitstream. -/
protected def readCLLengths : Nat → Nat → List Nat → List Bool →
    Option (List Nat × List Bool)
  | 0, _, acc, bits => some (acc, bits)
  | n + 1, idx, acc, bits => do
    let (val, bits) ← readBitsLSB 3 bits
    let pos := codeLengthOrder[idx]!
    let acc := acc.set pos val
    Deflate.Spec.readCLLengths n (idx + 1) acc bits

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
  let (clLengths, bits) ← Deflate.Spec.readCLLengths numCodeLen 0
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
    | fuel + 1 =>
      if acc.length ≥ totalCodes then some (acc, bits)
      else do
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

/-- Decode a complete DEFLATE stream: a sequence of blocks ending
    with a final block. Returns the concatenated output.
    Uses fuel to ensure termination.

    Note: LZ77 back-references can span block boundaries (RFC 1951 §3.2),
    so the accumulated output `acc` is passed to `resolveLZ77` for each
    Huffman block, not a fresh `[]`. -/
def decode (bits : List Bool) (fuel : Nat := 10001) :
    Option (List UInt8) :=
  go bits [] fuel
where
  go (bits : List Bool) (acc : List UInt8) :
      Nat → Option (List UInt8)
    | 0 => none
    | fuel + 1 => do
      let (bfinal, bits) ← readBitsLSB 1 bits
      let (btype, bits) ← readBitsLSB 2 bits
      match btype with
      | 0 => -- Stored block
        let (bytes, bits) ← decodeStored bits
        let acc := acc ++ bytes
        if bfinal == 1 then return acc else go bits acc fuel
      | 1 => -- Fixed Huffman
        let (syms, bits) ← decodeSymbols fixedLitLengths fixedDistLengths bits
        let acc ← resolveLZ77 syms acc
        if bfinal == 1 then return acc else go bits acc fuel
      | 2 => -- Dynamic Huffman
        let (litLens, distLens, bits) ← decodeDynamicTables bits
        let (syms, bits) ← decodeSymbols litLens distLens bits
        let acc ← resolveLZ77 syms acc
        if bfinal == 1 then return acc else go bits acc fuel
      | _ => none  -- reserved block type (3)

/-! ## Huffman encoding (inverse of decoding) -/

/-- Find the length code index for a given length (3–258).
    Returns `(index, extraBitsCount, extraBitsValue)` where
    the length code symbol is `257 + index`. -/
def findLengthCode (length : Nat) : Option (Nat × Nat × Nat) :=
  go 0
where
  go (i : Nat) : Option (Nat × Nat × Nat) :=
    if h : i ≥ lengthBase.size then none
    else
      let base := lengthBase[i]
      let nextBase := lengthBase[i + 1]?.getD 259
      if base ≤ length && length < nextBase then
        some (i, lengthExtra[i]!, length - base)
      else go (i + 1)
  termination_by lengthBase.size - i

/-- Find the distance code for a given distance (1–32768).
    Returns `(code, extraBitsCount, extraBitsValue)`. -/
def findDistCode (distance : Nat) : Option (Nat × Nat × Nat) :=
  go 0
where
  go (i : Nat) : Option (Nat × Nat × Nat) :=
    if h : i ≥ distBase.size then none
    else
      let base := distBase[i]
      let nextBase := distBase[i + 1]?.getD 32769
      if base ≤ distance && distance < nextBase then
        some (i, distExtra[i]!, distance - base)
      else go (i + 1)
  termination_by distBase.size - i

/-- Look up the Huffman codeword for a symbol in the code table.
    Returns the codeword or `none` if the symbol is not in the table. -/
def encodeSymbol (table : List (Huffman.Spec.Codeword × Nat))
    (sym : Nat) : Option (List Bool) :=
  match table with
  | [] => none
  | (cw, s) :: rest => if s == sym then some cw else encodeSymbol rest sym

/-- Encode one LZ77 symbol as Huffman-coded bits.
    Inverse of `decodeLitLen`. -/
def encodeLitLen (litLengths distLengths : List Nat)
    (sym : LZ77Symbol) : Option (List Bool) := do
  let litCodes := Huffman.Spec.allCodes litLengths
  let litTable := litCodes.map fun (s, cw) => (cw, s)
  match sym with
  | .literal b => encodeSymbol litTable b.toNat
  | .endOfBlock => encodeSymbol litTable 256
  | .reference len dist => do
    let (idx, extraN, extraV) ← findLengthCode len
    let lenBits ← encodeSymbol litTable (257 + idx)
    let distCodes := Huffman.Spec.allCodes distLengths
    let distTable := distCodes.map fun (s, cw) => (cw, s)
    let (dCode, dExtraN, dExtraV) ← findDistCode dist
    let distBits ← encodeSymbol distTable dCode
    return lenBits ++ writeBitsLSB extraN extraV ++
           distBits ++ writeBitsLSB dExtraN dExtraV

/-- Encode a list of LZ77 symbols as Huffman-coded bits. -/
def encodeSymbols (litLengths distLengths : List Nat)
    (syms : List LZ77Symbol) : Option (List Bool) :=
  match syms with
  | [] => some []
  | s :: rest => do
    let bits ← encodeLitLen litLengths distLengths s
    let restBits ← encodeSymbols litLengths distLengths rest
    return bits ++ restBits

/-! ## Encoding roundtrip theorems -/

/-- If `encodeSymbol` succeeds, the entry is in the table. -/
theorem encodeSymbol_mem (table : List (Huffman.Spec.Codeword × Nat))
    (sym : Nat) (cw : List Bool)
    (h : encodeSymbol table sym = some cw) :
    (cw, sym) ∈ table := by
  induction table with
  | nil => simp [encodeSymbol] at h
  | cons entry rest ih =>
    obtain ⟨cw', s'⟩ := entry
    simp only [encodeSymbol] at h
    split at h
    · rename_i heq
      have := beq_iff_eq.mp heq
      subst this; simp at h; subst h
      exact List.mem_cons_self ..
    · exact List.mem_cons_of_mem _ (ih h)

/-- Encoding then decoding a single Huffman symbol recovers it. -/
theorem encodeSymbol_decode
    (table : List (Huffman.Spec.Codeword × Nat))
    (sym : Nat) (cw : List Bool) (rest : List Bool)
    (henc : encodeSymbol table sym = some cw)
    (hpf : ∀ cw₁ s₁ cw₂ s₂, (cw₁, s₁) ∈ table → (cw₂, s₂) ∈ table →
      (cw₁, s₁) ≠ (cw₂, s₂) → ¬cw₁.IsPrefix cw₂) :
    Huffman.Spec.decode table (cw ++ rest) = some (sym, rest) :=
  Huffman.Spec.decode_prefix_free table cw sym rest (encodeSymbol_mem table sym cw henc) hpf

/-- The flipped allCodes table is prefix-free when lengths are valid. -/
theorem flipped_allCodes_prefix_free (lengths : List Nat) (maxBits : Nat)
    (hv : Huffman.Spec.ValidLengths lengths maxBits) :
    let table := (Huffman.Spec.allCodes lengths maxBits).map fun (s, cw) => (cw, s)
    ∀ cw₁ s₁ cw₂ s₂, (cw₁, s₁) ∈ table → (cw₂, s₂) ∈ table →
      (cw₁, s₁) ≠ (cw₂, s₂) → ¬cw₁.IsPrefix cw₂ := by
  intro table cw₁ s₁ cw₂ s₂ h₁ h₂ hne
  -- (cw, s) ∈ table means (s, cw) ∈ allCodes
  simp only [table, List.mem_map] at h₁ h₂
  obtain ⟨⟨a₁, b₁⟩, hm₁, heq₁⟩ := h₁
  obtain ⟨⟨a₂, b₂⟩, hm₂, heq₂⟩ := h₂
  simp at heq₁ heq₂
  obtain ⟨rfl, rfl⟩ := heq₁
  obtain ⟨rfl, rfl⟩ := heq₂
  -- Now: (b₁, a₁) ∈ allCodes, (b₂, a₂) ∈ allCodes, (b₁, a₁) ≠ (b₂, a₂)
  by_cases hse : a₁ = a₂
  · -- Same symbol → same codeword (codeFor is a function)
    subst hse
    rw [Huffman.Spec.allCodes_mem_iff] at hm₁ hm₂
    have := hm₁.2.symm.trans hm₂.2
    simp at this; subst this
    exact absurd rfl hne
  · exact Huffman.Spec.allCodes_prefix_free_of_ne lengths maxBits hv a₁ a₂ b₁ b₂ hm₁ hm₂ hse

set_option maxRecDepth 4096 in
/-- If Huffman decode gives a symbol < 256, `decodeLitLen` returns a literal. -/
theorem decodeLitLen_of_literal (litLengths distLengths : List Nat)
    (bits rest : List Bool) (sym : Nat)
    (hdec : Huffman.Spec.decode
      ((Huffman.Spec.allCodes litLengths).map fun (s, cw) => (cw, s))
      bits = some (sym, rest))
    (hlt : sym < 256) :
    decodeLitLen litLengths distLengths bits = some (.literal sym.toUInt8, rest) := by
  unfold decodeLitLen
  simp only [hdec, bind, Option.bind, if_pos hlt, pure, Pure.pure]

set_option maxRecDepth 4096 in
/-- If Huffman decode gives symbol 256, `decodeLitLen` returns endOfBlock. -/
theorem decodeLitLen_of_endOfBlock (litLengths distLengths : List Nat)
    (bits rest : List Bool)
    (hdec : Huffman.Spec.decode
      ((Huffman.Spec.allCodes litLengths).map fun (s, cw) => (cw, s))
      bits = some (256, rest)) :
    decodeLitLen litLengths distLengths bits = some (.endOfBlock, rest) := by
  unfold decodeLitLen
  simp only [hdec, bind, Option.bind, show ¬(256 : Nat) < 256 from by omega,
    if_false, show (256 : Nat) == 256 from rfl, if_true, pure, Pure.pure]

/-- Encoding then decoding one LZ77 symbol recovers it. -/
theorem encodeLitLen_decodeLitLen
    (litLengths distLengths : List Nat) (sym : LZ77Symbol)
    (bits rest : List Bool)
    (henc : encodeLitLen litLengths distLengths sym = some bits)
    (hvalid_lit : Huffman.Spec.ValidLengths litLengths 15)
    (hvalid_dist : Huffman.Spec.ValidLengths distLengths 15) :
    decodeLitLen litLengths distLengths (bits ++ rest) = some (sym, rest) := by
  have hpf_lit := flipped_allCodes_prefix_free litLengths 15 hvalid_lit
  cases sym with
  | literal b =>
    simp only [encodeLitLen] at henc
    have hdec := encodeSymbol_decode _ b.toNat bits rest henc hpf_lit
    have hlt : b.toNat < 256 := UInt8.toNat_lt b
    rw [decodeLitLen_of_literal litLengths distLengths (bits ++ rest) rest b.toNat hdec hlt]
    simp [UInt8.ofNat_toNat]
  | endOfBlock =>
    simp only [encodeLitLen] at henc
    have hdec := encodeSymbol_decode _ 256 bits rest henc hpf_lit
    exact decodeLitLen_of_endOfBlock litLengths distLengths (bits ++ rest) rest hdec
  | reference len dist =>
    -- The reference case requires proving consistency between
    -- findLengthCode/findDistCode and the decoder's table lookups,
    -- plus chaining four decode steps (lenCW, lenExtra, distCW, distExtra).
    -- Left as sorry — needs helper lemmas for findLengthCode_spec and
    -- findDistCode_spec connecting encoder table lookups to decoder lookups.
    sorry

/-- A symbol list is valid for decoding: ends with `.endOfBlock` and
    no `.endOfBlock` appears earlier. -/
def ValidSymbolList : List LZ77Symbol → Prop
  | [] => False
  | [.endOfBlock] => True
  | .endOfBlock :: _ => False
  | _ :: rest => ValidSymbolList rest

/-- Encoding then decoding a valid symbol sequence recovers it. -/
theorem encodeSymbols_decodeSymbols
    (litLengths distLengths : List Nat) (syms : List LZ77Symbol)
    (bits rest : List Bool) (fuel : Nat)
    (henc : encodeSymbols litLengths distLengths syms = some bits)
    (hvalid_lit : Huffman.Spec.ValidLengths litLengths 15)
    (hvalid_dist : Huffman.Spec.ValidLengths distLengths 15)
    (hfuel : fuel ≥ syms.length)
    (hvalid : ValidSymbolList syms) :
    decodeSymbols litLengths distLengths (bits ++ rest) fuel = some (syms, rest) := by
  induction syms generalizing bits fuel with
  | nil => exact absurd hvalid id
  | cons sym syms ih =>
    -- Extract encoding of head symbol and rest
    simp only [encodeSymbols] at henc
    cases hes : encodeLitLen litLengths distLengths sym with
    | none => simp [hes] at henc
    | some symBits =>
      simp only [hes, bind, Option.bind] at henc
      cases her : encodeSymbols litLengths distLengths syms with
      | none => simp [her] at henc
      | some restBits =>
        simp [her] at henc
        -- henc : bits = symBits ++ restBits
        subst henc
        -- fuel ≥ 1
        cases fuel with
        | zero => simp [List.length] at hfuel
        | succ f =>
          simp only [decodeSymbols]
          -- Reassociate: (symBits ++ restBits) ++ rest = symBits ++ (restBits ++ rest)
          rw [List.append_assoc]
          -- decodeLitLen recovers sym
          rw [encodeLitLen_decodeLitLen litLengths distLengths sym symBits
            (restBits ++ rest) hes hvalid_lit hvalid_dist]
          simp only [bind, Option.bind]
          -- Split on whether sym is endOfBlock
          cases sym with
          | endOfBlock =>
            -- Must be the last symbol
            cases syms with
            | nil =>
              simp [encodeSymbols] at her; subst her
              simp [pure, Pure.pure]
            | cons _ _ => exact absurd hvalid id
          | literal b =>
            have hvalid' : ValidSymbolList syms := by
              cases syms with
              | nil => exact absurd hvalid id
              | cons _ _ => exact hvalid
            rw [ih restBits f her (by simp [List.length] at hfuel ⊢; omega) hvalid']
            simp [pure, Pure.pure]
          | reference len dist =>
            have hvalid' : ValidSymbolList syms := by
              cases syms with
              | nil => exact absurd hvalid id
              | cons _ _ => exact hvalid
            rw [ih restBits f her (by simp [List.length] at hfuel ⊢; omega) hvalid']
            simp [pure, Pure.pure]

/-! ## Fuel independence -/

/-- `decodeSymbols` is fuel-independent: if it succeeds with some fuel,
    it returns the same result with any additional fuel. -/
theorem decodeSymbols_fuel_independent
    (litLengths distLengths : List Nat) (bits : List Bool)
    (fuel : Nat) (result : List LZ77Symbol × List Bool) :
    decodeSymbols litLengths distLengths bits fuel = some result →
    ∀ k, decodeSymbols litLengths distLengths bits (fuel + k) = some result := by
  intro h k
  induction fuel generalizing bits result with
  | zero => simp [decodeSymbols] at h
  | succ n ih =>
    -- Rewrite fuel arithmetic: (n + 1) + k = (n + k) + 1
    conv => lhs; rw [show n + 1 + k = (n + k) + 1 from by omega]
    unfold decodeSymbols at h ⊢
    cases hlit : decodeLitLen litLengths distLengths bits with
    | none => simp [hlit] at h
    | some p =>
      obtain ⟨sym, bits'⟩ := p
      simp only [hlit, bind, Option.bind] at h ⊢
      match sym with
      | .endOfBlock => exact h
      | .literal _ | .reference .. =>
        cases hrec : decodeSymbols litLengths distLengths bits' n with
        | none => simp [hrec] at h
        | some q =>
          obtain ⟨rest, bits''⟩ := q
          simp only [hrec] at h
          simp only [ih bits' (rest, bits'') hrec]
          exact h

/-- `decodeCLSymbols` is fuel-independent: if it succeeds with some fuel,
    it returns the same result with any additional fuel. -/
theorem decodeCLSymbols_fuel_independent
    (clTable : List (Huffman.Spec.Codeword × Nat))
    (totalCodes : Nat) (acc : List Nat) (bits : List Bool)
    (fuel : Nat) (result : List Nat × List Bool) :
    decodeDynamicTables.decodeCLSymbols clTable totalCodes acc bits fuel = some result →
    ∀ k, decodeDynamicTables.decodeCLSymbols clTable totalCodes acc bits (fuel + k) = some result := by
  intro h k
  induction fuel generalizing acc bits result with
  | zero => simp [decodeDynamicTables.decodeCLSymbols] at h
  | succ n ih =>
    conv => lhs; rw [show n + 1 + k = (n + k) + 1 from by omega]
    unfold decodeDynamicTables.decodeCLSymbols at h ⊢
    split
    · next hge =>
      -- h : if hge then some (acc, bits) else ... = some result
      rw [if_pos hge] at h
      exact h
    · next hlt =>
      rw [if_neg hlt] at h
      cases hdec : Huffman.Spec.decode clTable bits with
      | none => simp [hdec] at h
      | some p =>
        obtain ⟨sym, bits'⟩ := p
        simp only [hdec, bind, Option.bind] at h ⊢
        split
        · next hsym =>
          rw [if_pos hsym] at h
          exact ih _ _ _ h
        · next hsym =>
          rw [if_neg hsym] at h
          split
          · next hsym16 =>
            rw [if_pos hsym16] at h
            -- guard (acc.length > 0), readBitsLSB 2, guard (acc'.length ≤ totalCodes), rec
            by_cases hg : (0 : Nat) < acc.length
            · simp only [guard, hg, ↓reduceIte] at h ⊢
              cases hrb : readBitsLSB 2 bits' with
              | none => simp [hrb] at h
              | some q =>
                obtain ⟨rep, bits''⟩ := q
                simp only [hrb] at h ⊢
                by_cases hg2 : (acc ++ List.replicate (rep + 3) acc.getLast!).length ≤ totalCodes
                · simp only [hg2, ↓reduceIte] at h ⊢
                  exact ih _ _ _ h
                · simp only [hg2, ↓reduceIte] at h; simp at h
            · simp only [guard, hg, ↓reduceIte] at h; simp at h
          · next hsym16 =>
            rw [if_neg hsym16] at h
            split
            · next hsym17 =>
              rw [if_pos hsym17] at h
              -- readBitsLSB 3, guard (acc'.length ≤ totalCodes), rec
              cases hrb : readBitsLSB 3 bits' with
              | none => simp [hrb] at h
              | some q =>
                obtain ⟨rep, bits''⟩ := q
                simp only [hrb] at h ⊢
                by_cases hg : (acc ++ List.replicate (rep + 3) 0).length ≤ totalCodes
                · simp only [guard, hg, ↓reduceIte] at h ⊢
                  exact ih _ _ _ h
                · simp only [guard, hg, ↓reduceIte] at h; simp at h
            · next hsym17 =>
              rw [if_neg hsym17] at h
              split
              · next hsym18 =>
                rw [if_pos hsym18] at h
                -- readBitsLSB 7, guard (acc'.length ≤ totalCodes), rec
                cases hrb : readBitsLSB 7 bits' with
                | none => simp [hrb] at h
                | some q =>
                  obtain ⟨rep, bits''⟩ := q
                  simp only [hrb] at h ⊢
                  by_cases hg : (acc ++ List.replicate (rep + 11) 0).length ≤ totalCodes
                  · simp only [guard, hg, ↓reduceIte] at h ⊢
                    exact ih _ _ _ h
                  · simp only [guard, hg, ↓reduceIte] at h; simp at h
              · next hsym18 =>
                rw [if_neg hsym18] at h
                simp at h

set_option maxRecDepth 4096 in
/-- `decode` is fuel-independent: if it succeeds with some fuel,
    it returns the same result with any additional fuel. -/
private theorem decode_go_fuel_independent
    (bits : List Bool) (acc : List UInt8) (fuel : Nat) (result : List UInt8) :
    decode.go bits acc fuel = some result →
    ∀ k, decode.go bits acc (fuel + k) = some result := by
  intro h k
  induction fuel generalizing bits acc result with
  | zero => simp [decode.go] at h
  | succ n ih =>
    conv => lhs; rw [show n + 1 + k = (n + k) + 1 from by omega]
    unfold decode.go at h ⊢
    cases hbf : readBitsLSB 1 bits with
    | none => simp [hbf] at h
    | some p =>
      obtain ⟨bfinal, bits₁⟩ := p
      simp only [hbf, bind, Option.bind] at h ⊢
      cases hbt : readBitsLSB 2 bits₁ with
      | none => simp [hbt] at h
      | some q =>
        obtain ⟨btype, bits₂⟩ := q
        simp only [hbt] at h ⊢
        match hm : btype with
        | 0 =>
          cases hds : decodeStored bits₂ with
          | none => simp [hds] at h
          | some r =>
            obtain ⟨bytes, bits₃⟩ := r
            simp only [hds] at h ⊢
            split
            · next hbf1 => rw [if_pos hbf1] at h; exact h
            · next hbf1 => rw [if_neg hbf1] at h; exact ih _ _ _ h
        | 1 =>
          cases hsyms : decodeSymbols fixedLitLengths fixedDistLengths bits₂ with
          | none => simp [hsyms] at h
          | some r =>
            obtain ⟨syms, bits₃⟩ := r
            simp only [hsyms] at h ⊢
            cases hres : resolveLZ77 syms acc with
            | none => simp [hres] at h
            | some acc' =>
              simp only [hres] at h ⊢
              split
              · next hbf1 => rw [if_pos hbf1] at h; exact h
              · next hbf1 => rw [if_neg hbf1] at h; exact ih _ _ _ h
        | 2 =>
          cases hdt : decodeDynamicTables bits₂ with
          | none => simp [hdt] at h
          | some r =>
            obtain ⟨litLens, distLens, bits₃⟩ := r
            simp only [hdt] at h ⊢
            cases hsyms : decodeSymbols litLens distLens bits₃ with
            | none => simp [hsyms] at h
            | some s =>
              obtain ⟨syms, bits₄⟩ := s
              simp only [hsyms] at h ⊢
              cases hres : resolveLZ77 syms acc with
              | none => simp [hres] at h
              | some acc' =>
                simp only [hres] at h ⊢
                split
                · next hbf1 => rw [if_pos hbf1] at h; exact h
                · next hbf1 => rw [if_neg hbf1] at h; exact ih _ _ _ h
        | _ + 3 => simp at h

theorem decode_fuel_independent
    (bits : List Bool) (fuel : Nat) (result : List UInt8) :
    decode bits fuel = some result →
    ∀ k, decode bits (fuel + k) = some result := by
  intro h k
  exact decode_go_fuel_independent bits [] fuel result h k

/-! ## Correctness theorems -/

/-- Encoding stored blocks then decoding produces the original data. -/
theorem encodeStored_decode (data : List UInt8) :
    decode (encodeStored data) = some data := by sorry

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
