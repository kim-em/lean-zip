import Zip.Spec.HuffmanTheorems
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

/-- Encode a natural number as 16 bits in LSB-first order.
    Uses `testBit` directly for easier proofs with `readBitsLSB_ofFn_testBit`. -/
private def encodeLEU16 (v : Nat) : List Bool :=
  List.ofFn fun (i : Fin 16) => v.testBit i.val

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
    -- Single final block: BFINAL=1, BTYPE=00, 5 padding bits to byte-align
    [true, false, false] ++ List.replicate 5 false ++ encodeStoredBlock data
  else
    -- Non-final block with 65535 bytes, then recurse
    let block := data.take 65535
    let rest := data.drop 65535
    [false, false, false] ++ List.replicate 5 false ++
      encodeStoredBlock block ++ encodeStored rest
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
  -- Validate CL code lengths (reject oversubscribed codes, RFC 1951)
  guard (Huffman.Spec.ValidLengths clLengths 7)
  -- Decode the literal/length + distance lengths using the CL Huffman code
  let totalCodes := numLitLen + numDist
  let clCodes := Huffman.Spec.allCodes clLengths 7
  let clTable := clCodes.map fun (sym, cw) => (cw, sym)
  let (codeLengths, bits) ← decodeCLSymbols clTable totalCodes [] bits (totalCodes + 1)
  guard (codeLengths.length == totalCodes)
  let litLenLengths := codeLengths.take numLitLen
  let distLengths := codeLengths.drop numLitLen
  -- Validate lit/dist code lengths (reject oversubscribed codes)
  guard (Huffman.Spec.ValidLengths litLenLengths 15)
  guard (Huffman.Spec.ValidLengths distLengths 15)
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

set_option maxRecDepth 4096 in
/-- `decode.go` always extends the accumulator: if it succeeds, the
    result is an extension of the initial accumulator. -/
theorem decode_go_acc_prefix
    (bits : List Bool) (acc : List UInt8) (fuel : Nat) (result : List UInt8)
    (h : decode.go bits acc fuel = some result) :
    acc <+: result := by
  induction fuel generalizing bits acc result with
  | zero => simp [decode.go] at h
  | succ n ih =>
    unfold decode.go at h
    cases hbf : readBitsLSB 1 bits with
    | none => simp [hbf] at h
    | some p =>
      obtain ⟨bfinal, bits₁⟩ := p
      simp only [hbf, bind, Option.bind] at h
      cases hbt : readBitsLSB 2 bits₁ with
      | none => simp [hbt] at h
      | some q =>
        obtain ⟨btype, bits₂⟩ := q
        simp only [hbt] at h
        match hm : btype with
        | 0 =>
          cases hds : decodeStored bits₂ with
          | none => simp [hds] at h
          | some r =>
            obtain ⟨bytes, bits₃⟩ := r
            simp only [hds] at h
            split at h
            · simp [pure, Pure.pure] at h; exact h ▸ List.prefix_append _ _
            · exact List.IsPrefix.trans (List.prefix_append _ _) (ih _ _ _ h)
        | 1 =>
          cases hsyms : decodeSymbols fixedLitLengths fixedDistLengths bits₂ with
          | none => simp [hsyms] at h
          | some r =>
            obtain ⟨syms, bits₃⟩ := r
            simp only [hsyms] at h
            cases hres : resolveLZ77 syms acc with
            | none => simp [hres] at h
            | some acc' =>
              simp only [hres] at h
              have hacc' := resolveLZ77_extends syms acc acc' hres
              split at h
              · simp [pure, Pure.pure] at h; exact h ▸ hacc'
              · exact List.IsPrefix.trans hacc' (ih _ _ _ h)
        | 2 =>
          cases hdt : decodeDynamicTables bits₂ with
          | none => simp [hdt] at h
          | some r =>
            obtain ⟨litLens, distLens, bits₃⟩ := r
            simp only [hdt] at h
            cases hsyms : decodeSymbols litLens distLens bits₃ with
            | none => simp [hsyms] at h
            | some s =>
              obtain ⟨syms, bits₄⟩ := s
              simp only [hsyms] at h
              cases hres : resolveLZ77 syms acc with
              | none => simp [hres] at h
              | some acc' =>
                simp only [hres] at h
                have hacc' := resolveLZ77_extends syms acc acc' hres
                split at h
                · simp [pure, Pure.pure] at h; exact h ▸ hacc'
                · exact List.IsPrefix.trans hacc' (ih _ _ _ h)
        | _ + 3 => simp at h

theorem decode_fuel_independent
    (bits : List Bool) (fuel : Nat) (result : List UInt8) :
    decode bits fuel = some result →
    ∀ k, decode bits (fuel + k) = some result := by
  intro h k
  exact decode_go_fuel_independent bits [] fuel result h k

/-! ## Stored block roundtrip helpers -/

private theorem mod_two_mul (v m : Nat) (hm : m > 0) :
    v % (2 * m) = v % 2 + 2 * ((v / 2) % m) := by
  have key : v = (2 * m) * (v / 2 / m) + (2 * ((v / 2) % m) + v % 2) := by
    have h1 : 2 * (v / 2) + v % 2 = v := Nat.div_add_mod v 2
    have h2 : m * (v / 2 / m) + (v / 2) % m = v / 2 := Nat.div_add_mod (v / 2) m
    rw [← h2] at h1; rw [Nat.mul_add, ← Nat.mul_assoc] at h1; omega
  calc v % (2 * m)
      = ((2 * m) * (v / 2 / m) + (2 * ((v / 2) % m) + v % 2)) % (2 * m) := by rw [← key]
    _ = ((v / 2 / m) * (2 * m) + (2 * ((v / 2) % m) + v % 2)) % (2 * m) := by
        rw [Nat.mul_comm]
    _ = 2 * ((v / 2) % m) + v % 2 := Nat.mul_add_mod_of_lt (by
        have := Nat.mod_lt (v / 2) hm
        have := Nat.mod_lt v (show 0 < 2 by omega)
        omega)
    _ = v % 2 + 2 * ((v / 2) % m) := by omega

private theorem testBit_zero_eq_mod_two (v : Nat) :
    (if v.testBit 0 then 1 else 0) = v % 2 := by
  rw [Nat.testBit_zero]; split <;> rename_i h <;> simp_all <;> omega

/-- Reading `n` bits from the `testBit` encoding of `v` yields `v % 2^n`. -/
private theorem readBitsLSB_ofFn_testBit (v n : Nat) (rest : List Bool) :
    readBitsLSB n ((List.ofFn fun (i : Fin n) => v.testBit i.val) ++ rest) =
    some (v % 2^n, rest) := by
  induction n generalizing v with
  | zero => simp [readBitsLSB]; omega
  | succ k ih =>
    simp only [List.ofFn_succ, List.cons_append]
    have htail : (List.ofFn fun i : Fin k => Nat.testBit v (Fin.succ i).val) =
                 (List.ofFn fun i : Fin k => Nat.testBit (v / 2) i.val) := by
      congr 1; ext i; exact Nat.testBit_add_one v i.val
    rw [htail]
    show (readBitsLSB k _ |>.bind _) = _
    rw [ih (v / 2)]
    simp only [Option.bind, pure, Pure.pure]
    congr 1; congr 1
    simp only [show (0 : Fin (k + 1)).val = 0 from rfl]
    rw [testBit_zero_eq_mod_two,
        show (2:Nat)^(k+1) = 2 * 2^k from by rw [Nat.pow_succ, Nat.mul_comm],
        mod_two_mul v (2^k) Nat.one_le_two_pow]
    omega

/-- Reading 8 bits from `byteToBitsSpec b` recovers `b.toNat`. -/
private theorem readBitsLSB_byteToBitsSpec (b : UInt8) (rest : List Bool) :
    readBitsLSB 8 (byteToBitsSpec b ++ rest) = some (b.toNat, rest) := by
  have h := readBitsLSB_ofFn_testBit b.toNat 8 rest
  simp only [byteToBitsSpec] at h ⊢
  rw [h]; congr 1; congr 1
  exact Nat.mod_eq_of_lt (UInt8.toNat_lt b)

/-- `readNBytes` on `data.flatMap byteToBitsSpec` recovers `data`. -/
private theorem readNBytes_byteToBitsSpec (data : List UInt8) (rest : List Bool) :
    decodeStored.readNBytes data.length (data.flatMap byteToBitsSpec ++ rest) [] =
    some (data, rest) := by
  suffices ∀ (acc : List UInt8),
    decodeStored.readNBytes data.length (data.flatMap byteToBitsSpec ++ rest) acc =
    some (acc ++ data, rest) by simpa using this []
  induction data with
  | nil => intro acc; simp [decodeStored.readNBytes]
  | cons b bs ih =>
    intro acc
    simp only [List.flatMap_cons, List.length_cons, List.append_assoc]
    unfold decodeStored.readNBytes
    show (readBitsLSB 8 _ |>.bind _) = _
    rw [readBitsLSB_byteToBitsSpec]
    simp only [Option.bind]
    have : b.toNat.toUInt8 = b := by simp
    rw [this, ih (acc ++ [b])]
    simp [List.append_assoc]

/-- `data.flatMap byteToBitsSpec` has length `8 * data.length`. -/
private theorem flatMap_byteToBitsSpec_length (data : List UInt8) :
    (data.flatMap byteToBitsSpec).length = 8 * data.length := by
  induction data with
  | nil => simp
  | cons b bs ih =>
    simp only [List.flatMap_cons, List.length_append, byteToBitsSpec,
               List.length_ofFn, List.length_cons, ih]; omega

/-- `encodeStored` output length is always a multiple of 8. -/
private theorem encodeStored_length_mod8 (data : List UInt8) :
    (encodeStored data).length % 8 = 0 := by
  unfold encodeStored
  split
  · simp only [List.length_append, List.length_cons, List.length_nil,
               List.length_replicate, encodeStoredBlock, encodeLEU16,
               List.length_ofFn, flatMap_byteToBitsSpec_length]; omega
  · have ih := encodeStored_length_mod8 (data.drop 65535)
    simp only [List.length_append, List.length_cons, List.length_nil,
               List.length_replicate, List.length_take,
               encodeStoredBlock, encodeLEU16,
               List.length_ofFn, flatMap_byteToBitsSpec_length]; omega

/-- `decodeStored` on `[pad₅] ++ encodeStoredBlock data ++ rest` recovers `data`. -/
private theorem decodeStored_encodeStoredBlock (data : List UInt8) (rest : List Bool)
    (hlen : data.length ≤ 65535)
    (halign : (List.replicate 5 false ++ encodeStoredBlock data ++ rest).length % 8 = 5) :
    decodeStored (List.replicate 5 false ++ encodeStoredBlock data ++ rest) =
    some (data, rest) := by
  unfold decodeStored
  -- alignToByte drops 5 padding bits
  simp only [alignToByte]
  rw [halign]
  -- drop 5 from [false, false, false, false, false] ++ ...
  simp only [show List.replicate 5 false = [false, false, false, false, false] from rfl,
    List.cons_append, List.nil_append]
  simp only [List.drop_succ_cons, List.drop_zero]
  -- Now: readBitsLSB 16 (encodeLEU16 len ++ encodeLEU16 nlen ++ data.flatMap byteToBitsSpec ++ rest)
  simp only [encodeStoredBlock, encodeLEU16, List.append_assoc]
  show (readBitsLSB 16 _ |>.bind _) = _
  rw [readBitsLSB_ofFn_testBit data.length 16,
      show data.length % 2 ^ 16 = data.length from Nat.mod_eq_of_lt (by omega)]
  simp only [Option.bind]
  show (readBitsLSB 16 _ |>.bind _) = _
  rw [readBitsLSB_ofFn_testBit (data.length ^^^ 0xFFFF) 16,
      show (data.length ^^^ 0xFFFF) % 2 ^ 16 = data.length ^^^ 0xFFFF from
        Nat.mod_eq_of_lt (Nat.xor_lt_two_pow (by omega) (by omega))]
  simp only [Option.bind]
  rw [show (data.length ^^^ (data.length ^^^ 0xFFFF) == 0xFFFF) = true from by
    rw [← Nat.xor_assoc, Nat.xor_self, Nat.zero_xor]; decide]
  exact readNBytes_byteToBitsSpec data rest

/-! ## Correctness theorems -/

/-- Generalized roundtrip: `decode.go` on `encodeStored data` with
    accumulator `acc` and sufficient fuel produces `acc ++ data`. -/
private theorem encodeStored_go (data : List UInt8) (acc : List UInt8) (fuel : Nat)
    (hfuel : fuel ≥ data.length / 65535 + 1) :
    decode.go (encodeStored data) acc fuel = some (acc ++ data) := by
  induction data using encodeStored.induct generalizing acc fuel with
  | case1 data hle =>
    -- Single block: data.length ≤ 65535, BFINAL=1
    unfold encodeStored
    simp only [hle, ↓reduceIte]
    match fuel, hfuel with
    | fuel + 1, _ =>
    unfold decode.go
    -- Reduce BFINAL=1, BTYPE=00 header, match on btype=0, then bfinal==1 → return
    simp [readBitsLSB]
    -- Goal (cons-ified): (decodeStored (false::...::encodeStoredBlock data)).bind ... = ...
    have halign : (List.replicate 5 false ++ encodeStoredBlock data ++ []).length % 8 = 5 := by
      simp only [List.append_nil, List.length_append, List.length_replicate,
        encodeStoredBlock, encodeLEU16,
        List.length_ofFn, flatMap_byteToBitsSpec_length]; omega
    -- decodeStored_encodeStoredBlock with rest=[], then strip ++ []
    have hdec : decodeStored (List.replicate 5 false ++ encodeStoredBlock data) =
        some (data, []) := by
      have h := decodeStored_encodeStoredBlock data [] hle halign
      simp only [List.append_nil] at h; exact h
    -- Convert cons form back to replicate form for rewriting
    show (decodeStored (List.replicate 5 false ++ encodeStoredBlock data) |>.bind
      fun x => some (acc ++ x.fst)) = some (acc ++ data)
    rw [hdec]; simp
  | case2 data hgt rest ih =>
    -- Multi-block: data.length > 65535, BFINAL=0
    unfold encodeStored
    simp only [show ¬(data.length ≤ 65535) from by omega, ↓reduceIte]
    match fuel, hfuel with
    | fuel + 1, hfuel =>
    have htake_len : (data.take 65535).length = 65535 := by
      rw [List.length_take]; omega
    have hrest_len : rest.length = data.length - 65535 := by
      simp [show rest = data.drop 65535 from rfl]
    unfold decode.go
    -- Reduce BFINAL=0, BTYPE=00 header, match on btype=0
    simp [readBitsLSB]
    -- simp cons-ifies List.replicate and replaces rest with data.drop 65535;
    -- use change to convert back to the form expected by decodeStored_encodeStoredBlock
    change (decodeStored (List.replicate 5 false ++
        encodeStoredBlock (data.take 65535) ++ encodeStored rest) |>.bind
      fun x => decode.go x.snd (acc ++ x.fst) fuel) = some (acc ++ data)
    have halign : (List.replicate 5 false ++ encodeStoredBlock (data.take 65535) ++
        encodeStored rest).length % 8 = 5 := by
      simp only [List.length_append, List.length_replicate,
        encodeStoredBlock, encodeLEU16,
        List.length_ofFn, flatMap_byteToBitsSpec_length, htake_len]
      have := encodeStored_length_mod8 rest
      omega
    rw [decodeStored_encodeStoredBlock (data.take 65535) (encodeStored rest)
        (by omega) halign]
    simp only [Option.bind]
    rw [ih (acc ++ data.take 65535) fuel (by rw [hrest_len]; omega)]
    rw [List.append_assoc, show rest = data.drop 65535 from rfl, List.take_append_drop]

/-- Encoding stored blocks then decoding produces the original data.
    Uses explicit fuel `data.length / 65535 + 1` (≥ number of blocks).
    The default fuel (10001) suffices for data up to ~655MB;
    the theorem is stated with exact fuel to hold for all list lengths. -/
theorem encodeStored_decode (data : List UInt8) :
    decode (encodeStored data) (data.length / 65535 + 1) = some data := by
  unfold decode
  rw [encodeStored_go data [] (data.length / 65535 + 1) (by omega)]
  simp only [List.nil_append]

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

/-! ## Suffix invariance -/

/-- `readBitsLSB` is suffix-invariant: appending bits to the input
    appends them to the remainder. -/
theorem readBitsLSB_append (n : Nat) (bits suffix : List Bool)
    (val : Nat) (rest : List Bool)
    (h : readBitsLSB n bits = some (val, rest)) :
    readBitsLSB n (bits ++ suffix) = some (val, rest ++ suffix) := by
  induction n generalizing bits val rest with
  | zero =>
    simp [readBitsLSB] at h ⊢
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨rfl, rfl⟩
  | succ k ih =>
    cases bits with
    | nil => simp [readBitsLSB] at h
    | cons b bs =>
      simp only [readBitsLSB, List.cons_append] at h ⊢
      cases hk : readBitsLSB k bs with
      | none => simp [hk] at h
      | some p =>
        obtain ⟨v, rem⟩ := p
        simp [hk] at h
        obtain ⟨rfl, rfl⟩ := h
        rw [ih bs v rem hk]
        simp

/-- Prefix-free condition for a swapped `allCodes` table. -/
private theorem allCodes_swapped_prefix_free (lengths : List Nat) (maxBits : Nat)
    (hv : Huffman.Spec.ValidLengths lengths maxBits) :
    ∀ cw₁ s₁ cw₂ s₂,
      (cw₁, s₁) ∈ (Huffman.Spec.allCodes lengths maxBits).map (fun (sym, cw) => (cw, sym)) →
      (cw₂, s₂) ∈ (Huffman.Spec.allCodes lengths maxBits).map (fun (sym, cw) => (cw, sym)) →
      (cw₁, s₁) ≠ (cw₂, s₂) → ¬cw₁.IsPrefix cw₂ := by
  intro cw₁ s₁ cw₂ s₂ h₁ h₂ hne
  simp only [List.mem_map, Prod.mk.injEq] at h₁ h₂
  obtain ⟨⟨sym₁, cw₁'⟩, hmem₁, rfl, rfl⟩ := h₁
  obtain ⟨⟨sym₂, cw₂'⟩, hmem₂, rfl, rfl⟩ := h₂
  have hne_sym : sym₁ ≠ sym₂ := by
    intro heq; subst heq
    have hnd := Huffman.Spec.allCodes_nodup lengths maxBits
    have h₁' := hmem₁; have h₂' := hmem₂
    rw [Huffman.Spec.allCodes_mem_iff] at h₁' h₂'
    have := Option.some.inj (h₁'.2.symm.trans h₂'.2)
    exact hne (by subst this; rfl)
  exact Huffman.Spec.allCodes_prefix_free_of_ne lengths maxBits hv sym₁ sym₂ _ _ hmem₁ hmem₂ hne_sym

set_option maxRecDepth 2048 in
set_option linter.unusedSimpArgs false in
/-- `decodeLitLen` is suffix-invariant. -/
theorem decodeLitLen_append (litLengths distLengths : List Nat)
    (bits suffix : List Bool) (sym : LZ77Symbol) (rest : List Bool)
    (hvl : Huffman.Spec.ValidLengths litLengths 15)
    (hvd : Huffman.Spec.ValidLengths distLengths 15)
    (h : decodeLitLen litLengths distLengths bits = some (sym, rest)) :
    decodeLitLen litLengths distLengths (bits ++ suffix) = some (sym, rest ++ suffix) := by
  simp only [decodeLitLen] at h ⊢
  -- Thread through the Huffman lit decode
  cases hld : Huffman.Spec.decode ((Huffman.Spec.allCodes litLengths).map fun (sym, cw) => (cw, sym)) bits with
  | none => simp [hld] at h
  | some p =>
    obtain ⟨litSym, bits₁⟩ := p
    simp only [hld, bind, Option.bind] at h ⊢
    rw [Huffman.Spec.decode_suffix _ bits suffix litSym bits₁ hld
        (allCodes_swapped_prefix_free litLengths 15 hvl)]
    simp only [Option.bind] at h ⊢  -- needed: linter false positive
    by_cases hlit : litSym < 256
    · rw [if_pos hlit] at h ⊢
      obtain ⟨rfl, rfl⟩ := Option.some.inj h; rfl
    · rw [if_neg hlit] at h ⊢
      by_cases heob : (litSym == 256) = true
      · rw [if_pos heob] at h ⊢
        obtain ⟨rfl, rfl⟩ := Option.some.inj h; rfl
      · rw [if_neg heob] at h ⊢
        -- length/distance code — thread through do-notation
        cases hlb : lengthBase[litSym - 257]? with
        | none => simp [hlb] at h
        | some base =>
          simp only [hlb] at h ⊢
          cases hle : lengthExtra[litSym - 257]? with
          | none => simp [hle] at h
          | some extra =>
            simp only [hle] at h ⊢
            cases hrb : readBitsLSB extra bits₁ with
            | none => simp [hrb] at h
            | some q =>
              obtain ⟨extraVal, bits₂⟩ := q
              simp only [hrb] at h ⊢
              rw [readBitsLSB_append extra bits₁ suffix extraVal bits₂ hrb]
              cases hdd : Huffman.Spec.decode ((Huffman.Spec.allCodes distLengths).map fun (s, cw) => (cw, s)) bits₂ with
              | none => simp [hdd] at h
              | some r =>
                obtain ⟨dSym, bits₃⟩ := r
                simp only [hdd] at h ⊢
                rw [Huffman.Spec.decode_suffix _ bits₂ suffix dSym bits₃ hdd
                    (allCodes_swapped_prefix_free distLengths 15 hvd)]
                cases hdb : distBase[dSym]? with
                | none => simp [hdb] at h
                | some dBase =>
                  simp only [hdb] at h ⊢
                  cases hde : distExtra[dSym]? with
                  | none => simp [hde] at h
                  | some dExtra =>
                    simp only [hde] at h ⊢
                    cases hrbd : readBitsLSB dExtra bits₃ with
                    | none => simp [hrbd] at h
                    | some s =>
                      obtain ⟨dExtraVal, bits₄⟩ := s
                      simp only [hrbd] at h ⊢
                      rw [readBitsLSB_append dExtra bits₃ suffix dExtraVal bits₄ hrbd]
                      obtain ⟨rfl, rfl⟩ := Option.some.inj h; rfl

set_option linter.unusedSimpArgs false in
/-- `decodeSymbols` is suffix-invariant. -/
theorem decodeSymbols_append (litLengths distLengths : List Nat)
    (bits suffix : List Bool) (fuel : Nat)
    (syms : List LZ77Symbol) (rest : List Bool)
    (hvl : Huffman.Spec.ValidLengths litLengths 15)
    (hvd : Huffman.Spec.ValidLengths distLengths 15)
    (h : decodeSymbols litLengths distLengths bits fuel = some (syms, rest)) :
    decodeSymbols litLengths distLengths (bits ++ suffix) fuel =
      some (syms, rest ++ suffix) := by
  induction fuel generalizing bits syms rest with
  | zero => simp [decodeSymbols] at h
  | succ n ih =>
    unfold decodeSymbols at h ⊢
    cases hlit : decodeLitLen litLengths distLengths bits with
    | none => simp [hlit] at h
    | some p =>
      obtain ⟨sym, bits'⟩ := p
      simp only [hlit, bind, Option.bind] at h ⊢
      rw [decodeLitLen_append litLengths distLengths bits suffix sym bits' hvl hvd hlit]
      simp only [bind, Option.bind]
      match hsym : sym with
      | .endOfBlock =>
        obtain ⟨rfl, rfl⟩ := Option.some.inj h; rfl
      | .literal _ =>
        cases hrec : decodeSymbols litLengths distLengths bits' n with
        | none => simp [hrec] at h
        | some q =>
          obtain ⟨restSyms, bits''⟩ := q
          simp only [hrec] at h
          simp only [ih bits' restSyms bits'' hrec]
          obtain ⟨rfl, rfl⟩ := Option.some.inj h; rfl
      | .reference .. =>
        cases hrec : decodeSymbols litLengths distLengths bits' n with
        | none => simp [hrec] at h
        | some q =>
          obtain ⟨restSyms, bits''⟩ := q
          simp only [hrec] at h
          simp only [ih bits' restSyms bits'' hrec]
          obtain ⟨rfl, rfl⟩ := Option.some.inj h; rfl

set_option linter.unusedSimpArgs false in
/-- `readNBytes` is suffix-invariant. -/
private theorem readNBytes_append (n : Nat) (bits suffix : List Bool)
    (acc bytes : List UInt8) (rest : List Bool)
    (h : decodeStored.readNBytes n bits acc = some (bytes, rest)) :
    decodeStored.readNBytes n (bits ++ suffix) acc = some (bytes, rest ++ suffix) := by
  induction n generalizing bits acc bytes rest with
  | zero =>
    simp [decodeStored.readNBytes] at h ⊢
    obtain ⟨rfl, rfl⟩ := h; exact ⟨rfl, rfl⟩
  | succ k ih =>
    unfold decodeStored.readNBytes at h ⊢
    cases hrb : readBitsLSB 8 bits with
    | none => simp [hrb] at h
    | some p =>
      obtain ⟨v, bits'⟩ := p
      simp only [hrb, bind, Option.bind] at h ⊢
      rw [readBitsLSB_append 8 bits suffix v bits' hrb]
      simp only [bind, Option.bind]
      exact ih bits' (acc ++ [v.toUInt8]) bytes rest h

/-- `alignToByte (bits ++ suffix) = alignToByte bits ++ suffix`
    when `suffix.length % 8 = 0`. -/
private theorem alignToByte_append (bits suffix : List Bool)
    (hsuf : suffix.length % 8 = 0) :
    alignToByte (bits ++ suffix) = alignToByte bits ++ suffix := by
  simp only [alignToByte, List.length_append]
  rw [show (bits.length + suffix.length) % 8 = bits.length % 8 by omega]
  exact List.drop_append_of_le_length (Nat.mod_le _ _)

set_option linter.unusedSimpArgs false in
/-- `decodeStored` is suffix-invariant when suffix is byte-aligned. -/
theorem decodeStored_append (bits suffix : List Bool)
    (bytes : List UInt8) (rest : List Bool)
    (hsuf : suffix.length % 8 = 0)
    (h : decodeStored bits = some (bytes, rest)) :
    decodeStored (bits ++ suffix) = some (bytes, rest ++ suffix) := by
  simp only [decodeStored] at h ⊢
  rw [alignToByte_append bits suffix hsuf]
  -- Thread readBitsLSB 16 for LEN
  cases hrl : readBitsLSB 16 (alignToByte bits) with
  | none => simp [hrl] at h
  | some p =>
    obtain ⟨len, bits₁⟩ := p
    simp only [hrl, bind, Option.bind] at h ⊢
    rw [readBitsLSB_append 16 (alignToByte bits) suffix len bits₁ hrl]
    simp only [bind, Option.bind]
    -- Thread readBitsLSB 16 for NLEN
    cases hrn : readBitsLSB 16 bits₁ with
    | none => simp [hrn] at h
    | some q =>
      obtain ⟨nlen, bits₂⟩ := q
      simp only [hrn, bind, Option.bind] at h ⊢
      rw [readBitsLSB_append 16 bits₁ suffix nlen bits₂ hrn]
      simp only [bind, Option.bind]
      -- Guard passes identically
      by_cases hg : (len ^^^ nlen == 0xFFFF) = true
      · simp only [guard, hg, ↓reduceIte] at h ⊢
        exact readNBytes_append len bits₂ suffix [] bytes rest h
      · simp only [guard, hg, ↓reduceIte] at h; simp at h

/-- `readCLLengths` is suffix-invariant. -/
private theorem readCLLengths_append (n idx : Nat) (acc : List Nat)
    (bits suffix : List Bool)
    (result : List Nat) (rest : List Bool)
    (h : Deflate.Spec.readCLLengths n idx acc bits = some (result, rest)) :
    Deflate.Spec.readCLLengths n idx acc (bits ++ suffix) = some (result, rest ++ suffix) := by
  induction n generalizing idx acc bits result rest with
  | zero =>
    simp [Deflate.Spec.readCLLengths] at h ⊢
    obtain ⟨rfl, rfl⟩ := h; exact ⟨rfl, rfl⟩
  | succ k ih =>
    unfold Deflate.Spec.readCLLengths at h ⊢
    cases hrb : readBitsLSB 3 bits with
    | none => simp [hrb] at h
    | some p =>
      obtain ⟨v, bits'⟩ := p
      simp only [hrb, bind, Option.bind] at h ⊢
      rw [readBitsLSB_append 3 bits suffix v bits' hrb]
      simp only [bind, Option.bind]
      exact ih (idx + 1) (acc.set (codeLengthOrder[idx]!) v) bits' result rest h

set_option linter.unusedSimpArgs false in
/-- `decodeCLSymbols` is suffix-invariant. -/
private theorem decodeCLSymbols_append
    (clTable : List (Huffman.Spec.Codeword × Nat))
    (totalCodes : Nat) (acc : List Nat) (bits suffix : List Bool)
    (fuel : Nat) (result : List Nat) (rest : List Bool)
    (hpf : ∀ cw₁ s₁ cw₂ s₂, (cw₁, s₁) ∈ clTable → (cw₂, s₂) ∈ clTable →
      (cw₁, s₁) ≠ (cw₂, s₂) → ¬cw₁.IsPrefix cw₂)
    (h : decodeDynamicTables.decodeCLSymbols clTable totalCodes acc bits fuel =
      some (result, rest)) :
    decodeDynamicTables.decodeCLSymbols clTable totalCodes acc (bits ++ suffix) fuel =
      some (result, rest ++ suffix) := by
  induction fuel generalizing acc bits result rest with
  | zero => simp [decodeDynamicTables.decodeCLSymbols] at h
  | succ n ih =>
    unfold decodeDynamicTables.decodeCLSymbols at h ⊢
    by_cases hge : acc.length ≥ totalCodes
    · rw [if_pos hge] at h ⊢
      obtain ⟨rfl, rfl⟩ := Option.some.inj h; rfl
    · rw [if_neg hge] at h ⊢
      cases hdec : Huffman.Spec.decode clTable bits with
      | none => simp [hdec] at h
      | some p =>
        obtain ⟨sym, bits'⟩ := p
        simp only [hdec, bind, Option.bind] at h ⊢
        rw [Huffman.Spec.decode_suffix clTable bits suffix sym bits' hdec hpf]
        simp only [bind, Option.bind]
        by_cases hsym16 : sym < 16
        · rw [if_pos hsym16] at h ⊢
          exact ih (acc ++ [sym]) bits' result rest h
        · rw [if_neg hsym16] at h ⊢
          by_cases hsym16eq : (sym == 16) = true
          · rw [if_pos hsym16eq] at h ⊢
            by_cases hg : (0 : Nat) < acc.length
            · simp only [guard, hg, ↓reduceIte] at h ⊢
              cases hrb : readBitsLSB 2 bits' with
              | none => simp [hrb] at h
              | some q =>
                obtain ⟨rep, bits''⟩ := q
                simp only [hrb, bind, Option.bind] at h ⊢
                rw [readBitsLSB_append 2 bits' suffix rep bits'' hrb]
                simp only [bind, Option.bind]
                by_cases hg2 : (acc ++ List.replicate (rep + 3) acc.getLast!).length ≤ totalCodes
                · simp only [guard, hg2, ↓reduceIte] at h ⊢
                  exact ih _ bits'' result rest h
                · simp only [guard, hg2, ↓reduceIte] at h; simp at h
            · simp only [guard, hg, ↓reduceIte] at h; simp at h
          · rw [if_neg hsym16eq] at h ⊢
            by_cases hsym17 : (sym == 17) = true
            · rw [if_pos hsym17] at h ⊢
              cases hrb : readBitsLSB 3 bits' with
              | none => simp [hrb] at h
              | some q =>
                obtain ⟨rep, bits''⟩ := q
                simp only [hrb, bind, Option.bind] at h ⊢
                rw [readBitsLSB_append 3 bits' suffix rep bits'' hrb]
                simp only [bind, Option.bind]
                by_cases hg : (acc ++ List.replicate (rep + 3) 0).length ≤ totalCodes
                · simp only [guard, hg, ↓reduceIte] at h ⊢
                  exact ih _ bits'' result rest h
                · simp only [guard, hg, ↓reduceIte] at h; simp at h
            · rw [if_neg hsym17] at h ⊢
              by_cases hsym18 : (sym == 18) = true
              · rw [if_pos hsym18] at h ⊢
                cases hrb : readBitsLSB 7 bits' with
                | none => simp [hrb] at h
                | some q =>
                  obtain ⟨rep, bits''⟩ := q
                  simp only [hrb, bind, Option.bind] at h ⊢
                  rw [readBitsLSB_append 7 bits' suffix rep bits'' hrb]
                  simp only [bind, Option.bind]
                  by_cases hg : (acc ++ List.replicate (rep + 11) 0).length ≤ totalCodes
                  · simp only [guard, hg, ↓reduceIte] at h ⊢
                    exact ih _ bits'' result rest h
                  · simp only [guard, hg, ↓reduceIte] at h; simp at h
              · rw [if_neg hsym18] at h ⊢
                simp at h

set_option maxRecDepth 4096 in
set_option linter.unusedSimpArgs false in
/-- `decodeDynamicTables` is suffix-invariant. -/
theorem decodeDynamicTables_append (bits suffix : List Bool)
    (litLens distLens : List Nat) (rest : List Bool)
    (h : decodeDynamicTables bits = some (litLens, distLens, rest)) :
    decodeDynamicTables (bits ++ suffix) = some (litLens, distLens, rest ++ suffix) := by
  unfold decodeDynamicTables at h ⊢
  -- Process h through the first 3 readBitsLSB calls
  cases h5 : readBitsLSB 5 bits with
  | none => simp [h5] at h
  | some p₁ =>
    obtain ⟨hlit, bits₁⟩ := p₁
    cases h5d : readBitsLSB 5 bits₁ with
    | none => simp [h5, h5d] at h
    | some p₂ =>
      obtain ⟨hdist, bits₂⟩ := p₂
      cases h4 : readBitsLSB 4 bits₂ with
      | none => simp [h5, h5d, h4] at h
      | some p₃ =>
        obtain ⟨hclen, bits₃⟩ := p₃
        -- Process h: unfold expanded List.replicate to match hcl form
        -- h has a do-block, operations are inside nested match chains.
        -- We case on each operation and use one big simp to process h.
        -- Key: h has [0,...,0] literal, hcl has List.replicate 19 0.
        -- They are definitionally equal, so `have : literal_form = hcl_form := hcl`
        -- lets simp find the match in h.
        cases hcl : Deflate.Spec.readCLLengths (hclen + 4) 0
            (List.replicate 19 0) bits₃ with
        | none =>
          have hcl' : Spec.readCLLengths (hclen + 4) 0
              [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
              bits₃ = none := hcl
          simp [h5, h5d, h4, hcl'] at h
        | some p₄ =>
          obtain ⟨clLengths, bits₄⟩ := p₄
          have hcl' : Spec.readCLLengths (hclen + 4) 0
              [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
              bits₃ = some (clLengths, bits₄) := hcl
          by_cases hvCL : Huffman.Spec.ValidLengths clLengths 7
          · cases hcls : decodeDynamicTables.decodeCLSymbols
                ((Huffman.Spec.allCodes clLengths 7).map fun (sym, cw) => (cw, sym))
                (hlit + 257 + (hdist + 1)) [] bits₄
                (hlit + 257 + (hdist + 1) + 1) with
            | none =>
              simp [h5, h5d, h4, hcl', hvCL, hcls, guard, pure, Pure.pure] at h
            | some p₅ =>
              obtain ⟨codeLengths, bits₅⟩ := p₅
              by_cases hlen : codeLengths.length = hlit + 257 + (hdist + 1)
              · by_cases hvLL : Huffman.Spec.ValidLengths
                    (codeLengths.take (hlit + 257)) 15
                · by_cases hvDL : Huffman.Spec.ValidLengths
                      (codeLengths.drop (hlit + 257)) 15
                  · -- All operations succeed: extract result and build goal
                    have hlen_beq : (codeLengths.length == hlit + 257 + (hdist + 1)) = true :=
                      beq_iff_eq.mpr hlen
                    simp [h5, h5d, h4, hcl', hvCL, hcls, hlen, hlen_beq, hvLL, hvDL,
                          guard, pure, Pure.pure] at h
                    obtain ⟨rfl, rfl, rfl⟩ := h
                    -- Build the goal for bits ++ suffix
                    have h5' := readBitsLSB_append 5 bits suffix hlit bits₁ h5
                    have h5d' := readBitsLSB_append 5 bits₁ suffix hdist bits₂ h5d
                    have h4' := readBitsLSB_append 4 bits₂ suffix hclen bits₃ h4
                    have hcl_a := readCLLengths_append _ 0 _ bits₃ suffix clLengths bits₄ hcl
                    -- hcl_a has List.replicate, goal has literal; create literal form
                    have hcl_a' : Spec.readCLLengths (hclen + 4) 0
                        [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
                        (bits₃ ++ suffix) = some (clLengths, bits₄ ++ suffix) := hcl_a
                    have hcls' := decodeCLSymbols_append _ _ [] bits₄ suffix _
                        codeLengths bits₅
                        (allCodes_swapped_prefix_free clLengths 7 hvCL) hcls
                    simp [h5', h5d', h4', hcl_a', hvCL, hcls', hlen, hlen_beq, hvLL, hvDL,
                          guard, pure, Pure.pure]
                  · -- ¬hvDL: guard False makes h contradictory
                    have hlen_beq : (codeLengths.length == hlit + 257 + (hdist + 1)) = true :=
                      beq_iff_eq.mpr hlen
                    simp [h5, h5d, h4, hcl', hvCL, hcls, hlen, hlen_beq, hvLL, hvDL,
                          guard, pure, Pure.pure, failure, Alternative.failure] at h
                · -- ¬hvLL: guard False makes h contradictory
                  have hlen_beq : (codeLengths.length == hlit + 257 + (hdist + 1)) = true :=
                    beq_iff_eq.mpr hlen
                  simp [h5, h5d, h4, hcl', hvCL, hcls, hlen, hlen_beq, hvLL,
                        guard, pure, Pure.pure, failure, Alternative.failure] at h
              · -- ¬hlen: guard fails on length check
                have hlen_beq : (codeLengths.length == hlit + 257 + (hdist + 1)) = false := by
                  cases h_eq : (codeLengths.length == hlit + 257 + (hdist + 1)) <;> simp_all [beq_iff_eq]
                simp [h5, h5d, h4, hcl', hvCL, hcls, hlen, hlen_beq,
                      guard, pure, Pure.pure, failure, Alternative.failure] at h
          · -- ¬hvCL: guard fails on ValidLengths check
            simp [h5, h5d, h4, hcl', hvCL,
                  guard, pure, Pure.pure, failure, Alternative.failure] at h

set_option maxRecDepth 4096 in
set_option linter.unusedSimpArgs false in
/-- If `decodeDynamicTables` succeeds, the returned litLen lengths are valid. -/
theorem decodeDynamicTables_valid_lit (bits : List Bool)
    (litLens distLens : List Nat) (rest : List Bool)
    (h : decodeDynamicTables bits = some (litLens, distLens, rest)) :
    Huffman.Spec.ValidLengths litLens 15 := by
  unfold decodeDynamicTables at h
  cases h5 : readBitsLSB 5 bits with
  | none => simp [h5] at h
  | some p₁ =>
    obtain ⟨hlit, bits₁⟩ := p₁
    cases h5d : readBitsLSB 5 bits₁ with
    | none => simp [h5, h5d] at h
    | some p₂ =>
      obtain ⟨hdist, bits₂⟩ := p₂
      cases h4 : readBitsLSB 4 bits₂ with
      | none => simp [h5, h5d, h4] at h
      | some p₃ =>
        obtain ⟨hclen, bits₃⟩ := p₃
        cases hcl : Deflate.Spec.readCLLengths (hclen + 4) 0
            (List.replicate 19 0) bits₃ with
        | none =>
          have hcl' : Spec.readCLLengths (hclen + 4) 0
              [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
              bits₃ = none := hcl
          simp [h5, h5d, h4, hcl'] at h
        | some p₄ =>
          obtain ⟨clLengths, bits₄⟩ := p₄
          have hcl' : Spec.readCLLengths (hclen + 4) 0
              [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
              bits₃ = some (clLengths, bits₄) := hcl
          by_cases hvCL : Huffman.Spec.ValidLengths clLengths 7
          · cases hcls : decodeDynamicTables.decodeCLSymbols
                ((Huffman.Spec.allCodes clLengths 7).map fun (sym, cw) => (cw, sym))
                (hlit + 257 + (hdist + 1)) [] bits₄
                (hlit + 257 + (hdist + 1) + 1) with
            | none =>
              simp [h5, h5d, h4, hcl', hvCL, hcls, guard, pure, Pure.pure] at h
            | some p₅ =>
              obtain ⟨codeLengths, bits₅⟩ := p₅
              by_cases hlen : codeLengths.length = hlit + 257 + (hdist + 1)
              · have hlen_beq : (codeLengths.length == hlit + 257 + (hdist + 1)) = true :=
                  beq_iff_eq.mpr hlen
                by_cases hvLL : Huffman.Spec.ValidLengths
                    (codeLengths.take (hlit + 257)) 15
                · by_cases hvDL : Huffman.Spec.ValidLengths
                      (codeLengths.drop (hlit + 257)) 15
                  · simp [h5, h5d, h4, hcl', hvCL, hcls, hlen, hlen_beq, hvLL, hvDL,
                          guard, pure, Pure.pure] at h
                    exact h.1 ▸ hvLL
                  · simp [h5, h5d, h4, hcl', hvCL, hcls, hlen, hlen_beq, hvLL, hvDL,
                          guard, pure, Pure.pure, failure, Alternative.failure] at h
                · simp [h5, h5d, h4, hcl', hvCL, hcls, hlen, hlen_beq, hvLL,
                        guard, pure, Pure.pure, failure, Alternative.failure] at h
              · have hlen_beq : (codeLengths.length == hlit + 257 + (hdist + 1)) = false := by
                  cases h_eq : (codeLengths.length == hlit + 257 + (hdist + 1)) <;> simp_all [beq_iff_eq]
                simp [h5, h5d, h4, hcl', hvCL, hcls, hlen, hlen_beq,
                      guard, pure, Pure.pure, failure, Alternative.failure] at h
          · simp [h5, h5d, h4, hcl', hvCL,
                  guard, pure, Pure.pure, failure, Alternative.failure] at h

set_option maxRecDepth 4096 in
set_option linter.unusedSimpArgs false in
/-- If `decodeDynamicTables` succeeds, the returned distance lengths are valid. -/
theorem decodeDynamicTables_valid_dist (bits : List Bool)
    (litLens distLens : List Nat) (rest : List Bool)
    (h : decodeDynamicTables bits = some (litLens, distLens, rest)) :
    Huffman.Spec.ValidLengths distLens 15 := by
  unfold decodeDynamicTables at h
  cases h5 : readBitsLSB 5 bits with
  | none => simp [h5] at h
  | some p₁ =>
    obtain ⟨hlit, bits₁⟩ := p₁
    cases h5d : readBitsLSB 5 bits₁ with
    | none => simp [h5, h5d] at h
    | some p₂ =>
      obtain ⟨hdist, bits₂⟩ := p₂
      cases h4 : readBitsLSB 4 bits₂ with
      | none => simp [h5, h5d, h4] at h
      | some p₃ =>
        obtain ⟨hclen, bits₃⟩ := p₃
        cases hcl : Deflate.Spec.readCLLengths (hclen + 4) 0
            (List.replicate 19 0) bits₃ with
        | none =>
          have hcl' : Spec.readCLLengths (hclen + 4) 0
              [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
              bits₃ = none := hcl
          simp [h5, h5d, h4, hcl'] at h
        | some p₄ =>
          obtain ⟨clLengths, bits₄⟩ := p₄
          have hcl' : Spec.readCLLengths (hclen + 4) 0
              [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
              bits₃ = some (clLengths, bits₄) := hcl
          by_cases hvCL : Huffman.Spec.ValidLengths clLengths 7
          · cases hcls : decodeDynamicTables.decodeCLSymbols
                ((Huffman.Spec.allCodes clLengths 7).map fun (sym, cw) => (cw, sym))
                (hlit + 257 + (hdist + 1)) [] bits₄
                (hlit + 257 + (hdist + 1) + 1) with
            | none =>
              simp [h5, h5d, h4, hcl', hvCL, hcls, guard, pure, Pure.pure] at h
            | some p₅ =>
              obtain ⟨codeLengths, bits₅⟩ := p₅
              by_cases hlen : codeLengths.length = hlit + 257 + (hdist + 1)
              · have hlen_beq : (codeLengths.length == hlit + 257 + (hdist + 1)) = true :=
                  beq_iff_eq.mpr hlen
                by_cases hvLL : Huffman.Spec.ValidLengths
                    (codeLengths.take (hlit + 257)) 15
                · by_cases hvDL : Huffman.Spec.ValidLengths
                      (codeLengths.drop (hlit + 257)) 15
                  · simp [h5, h5d, h4, hcl', hvCL, hcls, hlen, hlen_beq, hvLL, hvDL,
                          guard, pure, Pure.pure] at h
                    exact h.2.1 ▸ hvDL
                  · simp [h5, h5d, h4, hcl', hvCL, hcls, hlen, hlen_beq, hvLL, hvDL,
                          guard, pure, Pure.pure, failure, Alternative.failure] at h
                · simp [h5, h5d, h4, hcl', hvCL, hcls, hlen, hlen_beq, hvLL,
                        guard, pure, Pure.pure, failure, Alternative.failure] at h
              · have hlen_beq : (codeLengths.length == hlit + 257 + (hdist + 1)) = false := by
                  cases h_eq : (codeLengths.length == hlit + 257 + (hdist + 1)) <;> simp_all [beq_iff_eq]
                simp [h5, h5d, h4, hcl', hvCL, hcls, hlen, hlen_beq,
                      guard, pure, Pure.pure, failure, Alternative.failure] at h
          · simp [h5, h5d, h4, hcl', hvCL,
                  guard, pure, Pure.pure, failure, Alternative.failure] at h

set_option maxRecDepth 4096 in
set_option linter.unusedSimpArgs false in
/-- `decode.go` is suffix-invariant: appending bits after a valid stream
    yields the same decoded result with the extra bits ignored.
    Requires `suffix.length % 8 = 0` for stored blocks (btype = 0). -/
theorem decode_go_suffix
    (bits suffix : List Bool) (acc : List UInt8) (fuel : Nat) (result : List UInt8)
    (hsuf : suffix.length % 8 = 0)
    (h : decode.go bits acc fuel = some result) :
    decode.go (bits ++ suffix) acc fuel = some result := by
  induction fuel generalizing bits acc result with
  | zero => simp [decode.go] at h
  | succ n ih =>
    unfold decode.go at h ⊢
    cases hbf : readBitsLSB 1 bits with
    | none => simp [hbf] at h
    | some p =>
      obtain ⟨bfinal, bits₁⟩ := p
      simp only [hbf, bind, Option.bind] at h ⊢
      rw [readBitsLSB_append 1 bits suffix bfinal bits₁ hbf]
      simp only [bind, Option.bind]
      cases hbt : readBitsLSB 2 bits₁ with
      | none => simp [hbt] at h
      | some q =>
        obtain ⟨btype, bits₂⟩ := q
        simp only [hbt, bind, Option.bind] at h
        rw [readBitsLSB_append 2 bits₁ suffix btype bits₂ hbt]
        simp only [bind, Option.bind]
        match hm : btype with
        | 0 => -- Stored block
          cases hds : decodeStored bits₂ with
          | none => simp [hds] at h
          | some r =>
            obtain ⟨bytes, bits₃⟩ := r
            simp only [hds, bind, Option.bind] at h
            rw [decodeStored_append bits₂ suffix bytes bits₃ hsuf hds]
            simp only [bind, Option.bind]
            by_cases hbf1 : (bfinal == 1) = true
            · rw [if_pos hbf1] at h ⊢; exact h
            · rw [if_neg hbf1] at h ⊢; exact ih _ _ _ h
        | 1 => -- Fixed Huffman
          cases hsyms : decodeSymbols fixedLitLengths fixedDistLengths bits₂ with
          | none => simp [hsyms] at h
          | some r =>
            obtain ⟨syms, bits₃⟩ := r
            simp only [hsyms, bind, Option.bind] at h
            rw [decodeSymbols_append fixedLitLengths fixedDistLengths bits₂ suffix _
                syms bits₃ fixedLitLengths_valid fixedDistLengths_valid hsyms]
            simp only [bind, Option.bind]
            cases hres : resolveLZ77 syms acc with
            | none => simp [hres] at h
            | some acc' =>
              simp only [hres, bind, Option.bind] at h ⊢
              by_cases hbf1 : (bfinal == 1) = true
              · rw [if_pos hbf1] at h ⊢; exact h
              · rw [if_neg hbf1] at h ⊢; exact ih _ _ _ h
        | 2 => -- Dynamic Huffman
          cases hdt : decodeDynamicTables bits₂ with
          | none => simp [hdt] at h
          | some r =>
            obtain ⟨litLens, distLens, bits₃⟩ := r
            simp only [hdt, bind, Option.bind] at h
            rw [decodeDynamicTables_append bits₂ suffix litLens distLens bits₃ hdt]
            simp only [bind, Option.bind]
            cases hsyms : decodeSymbols litLens distLens bits₃ with
            | none => simp [hsyms] at h
            | some s =>
              obtain ⟨syms, bits₄⟩ := s
              simp only [hsyms, bind, Option.bind] at h
              rw [decodeSymbols_append litLens distLens bits₃ suffix _
                  syms bits₄
                  (decodeDynamicTables_valid_lit bits₂ litLens distLens bits₃ hdt)
                  (decodeDynamicTables_valid_dist bits₂ litLens distLens bits₃ hdt) hsyms]
              simp only [bind, Option.bind]
              cases hres : resolveLZ77 syms acc with
              | none => simp [hres] at h
              | some acc' =>
                simp only [hres, bind, Option.bind] at h ⊢
                by_cases hbf1 : (bfinal == 1) = true
                · rw [if_pos hbf1] at h ⊢; exact h
                · rw [if_neg hbf1] at h ⊢; exact ih _ _ _ h
        | _ + 3 => simp at h

end Deflate.Spec
