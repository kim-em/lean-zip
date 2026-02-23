import Zip.Spec.Deflate
import Zip.Spec.BitstreamCorrect

/-!
# DEFLATE Encoding Specification

Huffman symbol encoding functions and roundtrip theorems for DEFLATE.
Includes:
- Length/distance table lookup (`findLengthCode`, `findDistCode`)
- Symbol encoding (`encodeSymbol`, `encodeLitLen`, `encodeSymbols`)
- Encoding roundtrip theorems (`encodeLitLen_decodeLitLen`, `encodeSymbols_decodeSymbols`)
- Fixed Huffman block encoder (`encodeFixed`) and success proofs

LZ77→encode bridge proofs and lazy matcher are in `Zip.Spec.LZ77Lazy`.
-/

namespace Deflate.Spec

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

/-- Reading back bits written by `writeBitsLSB` recovers the original value. -/
private theorem readBitsLSB_writeBitsLSB (n val : Nat) (rest : List Bool)
    (h : val < 2 ^ n) :
    readBitsLSB n (writeBitsLSB n val ++ rest) = some (val, rest) := by
  induction n generalizing val with
  | zero => simp [readBitsLSB, writeBitsLSB]; omega
  | succ k ih =>
    simp only [writeBitsLSB, List.cons_append, readBitsLSB]
    have hlt : val / 2 < 2 ^ k := by
      rw [Nat.div_lt_iff_lt_mul (by omega : 0 < 2)]; rw [Nat.pow_succ] at h; omega
    rw [ih (val / 2) hlt]
    simp only [bind, Option.bind]
    congr 1; ext1
    · have := Nat.div_add_mod val 2
      split <;> simp_all [beq_iff_eq] <;> omega
    · rfl

/-- Properties of `findLengthCode.go`: the returned index is valid,
    extra bits count and value are consistent with the tables. -/
private theorem findLengthCode_go_spec (len i idx extraN extraV : Nat)
    (h : findLengthCode.go len i = some (idx, extraN, extraV)) :
    idx < lengthBase.size ∧
    extraN = lengthExtra[idx]! ∧
    lengthBase[idx]! + extraV = len ∧
    len < (lengthBase[idx + 1]?.getD 259) := by
  unfold findLengthCode.go at h
  split at h
  · exact absurd h (by simp)
  · rename_i hi
    simp only [letFun] at h
    split at h
    · rename_i hcond
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hcond
      refine ⟨by omega, rfl, ?_, hcond.2⟩
      rw [getElem!_pos lengthBase i (by omega)]; omega
    · exact findLengthCode_go_spec len (i + 1) idx extraN extraV h
termination_by lengthBase.size - i

/-- The length table gaps are bounded by 2^extra: for each valid index i,
    the range of lengths mapping to that index fits in `lengthExtra[i]` bits. -/
private theorem lengthTable_gap :
    ∀ i : Fin 29, (lengthBase[i.val + 1]?.getD 259) - lengthBase[i.val]! ≤
      2 ^ lengthExtra[i.val]! := by decide

/-- `findLengthCode` returns a valid index with consistent extra bits. -/
theorem findLengthCode_spec (len idx extraN extraV : Nat)
    (h : findLengthCode len = some (idx, extraN, extraV)) :
    idx < 29 ∧
    lengthBase[idx]! + extraV = len ∧
    extraN = lengthExtra[idx]! ∧
    extraV < 2 ^ extraN := by
  have hgo := findLengthCode_go_spec len 0 idx extraN extraV h
  have hidx : idx < 29 := by simp [lengthBase] at hgo; exact hgo.1
  refine ⟨hidx, hgo.2.2.1, hgo.2.1, ?_⟩
  have hgap := lengthTable_gap ⟨idx, hidx⟩
  simp only [Fin.val_mk] at hgap
  rw [hgo.2.1]  -- extraN → lengthExtra[idx]!
  omega

/-- Properties of `findDistCode.go`: analogous to `findLengthCode_go_spec`. -/
private theorem findDistCode_go_spec (dist i idx extraN extraV : Nat)
    (h : findDistCode.go dist i = some (idx, extraN, extraV)) :
    idx < distBase.size ∧
    extraN = distExtra[idx]! ∧
    distBase[idx]! + extraV = dist ∧
    dist < (distBase[idx + 1]?.getD 32769) := by
  unfold findDistCode.go at h
  split at h
  · exact absurd h (by simp)
  · rename_i hi
    simp only [letFun] at h
    split at h
    · rename_i hcond
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hcond
      refine ⟨by omega, rfl, ?_, hcond.2⟩
      rw [getElem!_pos distBase i (by omega)]; omega
    · exact findDistCode_go_spec dist (i + 1) idx extraN extraV h
termination_by distBase.size - i

/-- The distance table gaps are bounded by 2^extra. -/
private theorem distTable_gap :
    ∀ i : Fin 30, (distBase[i.val + 1]?.getD 32769) - distBase[i.val]! ≤
      2 ^ distExtra[i.val]! := by decide

/-- `findDistCode` returns a valid index with consistent extra bits. -/
theorem findDistCode_spec (dist idx extraN extraV : Nat)
    (h : findDistCode dist = some (idx, extraN, extraV)) :
    idx < 30 ∧
    distBase[idx]! + extraV = dist ∧
    extraN = distExtra[idx]! ∧
    extraV < 2 ^ extraN := by
  have hgo := findDistCode_go_spec dist 0 idx extraN extraV h
  have hidx : idx < 30 := by simp [distBase] at hgo; exact hgo.1
  refine ⟨hidx, hgo.2.2.1, hgo.2.1, ?_⟩
  have hgap := distTable_gap ⟨idx, hidx⟩
  simp only [Fin.val_mk] at hgap
  rw [hgo.2.1]  -- extraN → distExtra[idx]!
  omega

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

set_option maxRecDepth 4096 in
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
    -- Extract encoder intermediate results
    simp only [encodeLitLen, bind, Option.bind] at henc
    -- Split on findLengthCode
    cases hfl : findLengthCode len with
    | none => simp [hfl] at henc
    | some lenResult =>
      obtain ⟨idx, extraN, extraV⟩ := lenResult
      simp only [hfl] at henc
      -- Split on encodeSymbol for length code
      cases hels : encodeSymbol
          ((Huffman.Spec.allCodes litLengths).map fun x => (x.2, x.1))
          (257 + idx) with
      | none => simp [hels] at henc
      | some lenBits =>
        simp only [hels] at henc
        -- Split on findDistCode
        cases hfd : findDistCode dist with
        | none => simp [hfd] at henc
        | some distResult =>
          obtain ⟨dCode, dExtraN, dExtraV⟩ := distResult
          simp only [hfd] at henc
          -- Split on encodeSymbol for distance code
          cases heds : encodeSymbol
              ((Huffman.Spec.allCodes distLengths).map fun x => (x.2, x.1))
              dCode with
          | none => simp [heds] at henc
          | some distBits =>
            simp only [heds, pure, Pure.pure, Option.some.injEq] at henc
            -- henc : bits = lenBits ++ writeBitsLSB extraN extraV ++
            --               distBits ++ writeBitsLSB dExtraN dExtraV
            subst henc
            -- Get spec properties from helper lemmas
            have hlspec := findLengthCode_spec len idx extraN extraV hfl
            have hdspec := findDistCode_spec dist dCode dExtraN dExtraV hfd
            -- hlspec: idx < 29, lengthBase[idx]! + extraV = len,
            --         extraN = lengthExtra[idx]!, extraV < 2^extraN
            -- hdspec: dCode < 30, distBase[dCode]! + dExtraV = dist,
            --         dExtraN = distExtra[dCode]!, dExtraV < 2^dExtraN
            have hpf_dist := flipped_allCodes_prefix_free distLengths 15 hvalid_dist
            -- Bounds for table indices
            have hidx : idx < lengthBase.size := by simp [lengthBase]; omega
            have hidxE : idx < lengthExtra.size := by simp [lengthExtra]; omega
            have hdCode : dCode < distBase.size := by simp [distBase]; omega
            have hdCodeE : dCode < distExtra.size := by simp [distExtra]; omega
            -- Normalize getElem! to getElem in spec hypotheses
            rw [getElem!_pos lengthBase idx hidx] at hlspec
            rw [getElem!_pos lengthExtra idx hidxE] at hlspec
            rw [getElem!_pos distBase dCode hdCode] at hdspec
            rw [getElem!_pos distExtra dCode hdCodeE] at hdspec
            -- Destructure spec results, substituting extraN/dExtraN
            obtain ⟨_, hlenSum, rfl, hextraV⟩ := hlspec
            obtain ⟨_, hdistSum, rfl, hdExtraV⟩ := hdspec
            -- Unfold decodeLitLen and fully reassociate appends
            unfold decodeLitLen
            simp only [List.append_assoc]
            -- Step 1: Huffman decode for length symbol (257 + idx)
            rw [encodeSymbol_decode _ (257 + idx) lenBits
              (writeBitsLSB lengthExtra[idx] extraV ++
               (distBits ++ (writeBitsLSB distExtra[dCode] dExtraV ++ rest)))
              hels hpf_lit]
            simp only [bind, Option.bind]
            -- sym = 257 + idx ≥ 257, so not < 256 and not == 256
            rw [if_neg (by omega : ¬(257 + idx < 256))]
            rw [if_neg (show ¬((257 + idx == 256) = true) by
              simp [beq_iff_eq]; omega)]
            -- idx = (257 + idx) - 257
            simp only [show 257 + idx - 257 = idx from by omega]
            -- The do-notation expanded as nested match expressions.
            -- Use have + dsimp to resolve each step.
            -- Step 2: Read extra length bits
            have hrd2 : readBitsLSB lengthExtra[idx]
              (writeBitsLSB lengthExtra[idx] extraV ++
               (distBits ++ (writeBitsLSB distExtra[dCode] dExtraV ++ rest))) =
              some (extraV, distBits ++
               (writeBitsLSB distExtra[dCode] dExtraV ++ rest)) :=
              readBitsLSB_writeBitsLSB _ _ _ hextraV
            -- Table lookups
            have hlb : lengthBase[idx]? = some lengthBase[idx] :=
              getElem?_pos lengthBase idx hidx
            have hle : lengthExtra[idx]? = some lengthExtra[idx] :=
              getElem?_pos lengthExtra idx hidxE
            -- Step 3: Huffman decode for distance
            have hrd3 : Huffman.Spec.decode
              ((Huffman.Spec.allCodes distLengths).map fun (s, cw) => (cw, s))
              (distBits ++ (writeBitsLSB distExtra[dCode] dExtraV ++ rest)) =
              some (dCode, writeBitsLSB distExtra[dCode] dExtraV ++ rest) :=
              encodeSymbol_decode _ dCode distBits _ heds hpf_dist
            have hdb : distBase[dCode]? = some distBase[dCode] :=
              getElem?_pos distBase dCode hdCode
            have hde : distExtra[dCode]? = some distExtra[dCode] :=
              getElem?_pos distExtra dCode hdCodeE
            -- Step 4: Read extra distance bits
            have hrd4 : readBitsLSB distExtra[dCode]
              (writeBitsLSB distExtra[dCode] dExtraV ++ rest) =
              some (dExtraV, rest) :=
              readBitsLSB_writeBitsLSB _ _ _ hdExtraV
            simp [hlb, hle, hrd2, hrd3, hdb, hde, hrd4, pure, Pure.pure]
            exact ⟨hlenSum, hdistSum⟩

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

/-! ## Fixed Huffman block encoding -/

/-- Encode a list of LZ77 symbols as a single fixed-Huffman DEFLATE block.
    Produces BFINAL=1 + BTYPE=01 header followed by Huffman-coded symbols.
    Returns `none` if any symbol cannot be encoded. -/
def encodeFixed (syms : List LZ77Symbol) : Option (List Bool) := do
  let bits ← encodeSymbols fixedLitLengths fixedDistLengths syms
  return [true, true, false] ++ bits

/-! ## Header readback lemmas -/

private theorem readBitsLSB_1_true (rest : List Bool) :
    readBitsLSB 1 (true :: rest) = some (1, rest) := by
  simp [readBitsLSB]

private theorem readBitsLSB_2_true_false (rest : List Bool) :
    readBitsLSB 2 (true :: false :: rest) = some (1, rest) := by
  simp [readBitsLSB]

/-! ## Encoding roundtrip theorems -/

/-- Encoding with fixed Huffman then decoding recovers the original data. -/
theorem encodeFixed_decode (syms : List LZ77Symbol) (data : List UInt8)
    (bits : List Bool)
    (henc : encodeSymbols fixedLitLengths fixedDistLengths syms = some bits)
    (hresolve : resolveLZ77 syms [] = some data)
    (hfuel : 10000000 ≥ syms.length)
    (hvalid : ValidSymbolList syms) :
    decode ([true, true, false] ++ bits) = some data := by
  -- Unfold one step of decode.go
  show decode.go ([true, true, false] ++ bits) [] 10001 = some data
  unfold decode.go
  -- readBitsLSB 1 ([true, true, false] ++ bits) = some (1, [true, false] ++ bits)
  simp only [List.cons_append, readBitsLSB_1_true, bind, Option.bind]
  -- readBitsLSB 2 ([true, false] ++ bits) = some (1, bits)
  simp only [readBitsLSB_2_true_false]
  -- Now in btype = 1 (fixed Huffman) branch
  have hdec : decodeSymbols fixedLitLengths fixedDistLengths bits
      10000000 = some (syms, []) := by
    have := encodeSymbols_decodeSymbols fixedLitLengths fixedDistLengths syms bits []
      10000000 henc fixedLitLengths_valid fixedDistLengths_valid hfuel hvalid
    rwa [List.append_nil] at this
  simp only [List.nil_append]
  rw [hdec]
  simp only [hresolve]
  simp [pure, Pure.pure]

/-! ## encodeSymbol succeeds when symbol is in the table -/

/-- `encodeSymbol` succeeds when the symbol is in the table. -/
theorem encodeSymbol_isSome (table : List (Huffman.Spec.Codeword × Nat))
    (sym : Nat) (cw : Huffman.Spec.Codeword)
    (h : (cw, sym) ∈ table) :
    (encodeSymbol table sym).isSome = true := by
  induction table with
  | nil => simp at h
  | cons entry rest ih =>
    obtain ⟨cw', s'⟩ := entry
    simp only [encodeSymbol]
    split
    · simp
    · rename_i hne
      simp only [beq_iff_eq] at hne
      simp only [List.mem_cons, Prod.mk.injEq] at h
      exact h.elim (fun heq => absurd heq.2.symm hne) ih

/-- `encodeSymbol` on a flipped `allCodes` table succeeds when the symbol
    has a non-zero code length. -/
theorem encodeSymbol_fixed_isSome (lengths : List Nat) (maxBits : Nat)
    (sym : Nat) (hsym : sym < lengths.length)
    (hlen : lengths[sym]! ≠ 0) (hmb : lengths[sym]! ≤ maxBits) :
    (encodeSymbol
      ((Huffman.Spec.allCodes lengths maxBits).map fun (s, cw) => (cw, s))
      sym).isSome = true := by
  have hcf : Huffman.Spec.codeFor lengths maxBits sym ≠ none := by
    simp only [Huffman.Spec.codeFor, dif_pos hsym]
    rw [getElem!_pos lengths sym hsym] at hlen hmb
    simp [hlen, hmb]
  obtain ⟨cw, hcw⟩ := Option.ne_none_iff_exists'.mp hcf
  have hmem : (sym, cw) ∈ Huffman.Spec.allCodes lengths maxBits :=
    (Huffman.Spec.allCodes_mem_iff ..).mpr ⟨hsym, hcw⟩
  have : (cw, sym) ∈ (Huffman.Spec.allCodes lengths maxBits).map fun (s, cw) => (cw, s) := by
    simp only [List.mem_map]
    exact ⟨(sym, cw), hmem, rfl⟩
  exact encodeSymbol_isSome _ _ _ this

/-! ## findLengthCode and findDistCode coverage -/

/-! ## Fixed table properties -/

/-- All entries in `fixedLitLengths` are between 1 and 15. -/
theorem fixedLitLengths_entry_bounds :
    ∀ x ∈ fixedLitLengths, 1 ≤ x ∧ x ≤ 15 := by
  simp only [fixedLitLengths, List.mem_append, List.mem_replicate]
  intro x hx
  cases hx with
  | inl h => cases h with
    | inl h => cases h with
      | inl h => exact ⟨by omega, by omega⟩
      | inr h => exact ⟨by omega, by omega⟩
    | inr h => exact ⟨by omega, by omega⟩
  | inr h => exact ⟨by omega, by omega⟩

/-- All entries in `fixedDistLengths` are between 1 and 15. -/
theorem fixedDistLengths_entry_bounds :
    ∀ x ∈ fixedDistLengths, 1 ≤ x ∧ x ≤ 15 := by
  simp only [fixedDistLengths, List.mem_replicate]
  omega

/-- For any valid index into fixedLitLengths, the entry is non-zero. -/
theorem fixedLitLengths_getElem_pos (i : Nat) (h : i < fixedLitLengths.length) :
    fixedLitLengths[i]! ≥ 1 := by
  rw [getElem!_pos fixedLitLengths i h]
  have := fixedLitLengths_entry_bounds (fixedLitLengths[i]) (List.getElem_mem h)
  exact this.1

/-- For any valid index into fixedLitLengths, the entry is ≤ 15. -/
theorem fixedLitLengths_getElem_le (i : Nat) (h : i < fixedLitLengths.length) :
    fixedLitLengths[i]! ≤ 15 := by
  rw [getElem!_pos fixedLitLengths i h]
  have := fixedLitLengths_entry_bounds (fixedLitLengths[i]) (List.getElem_mem h)
  exact this.2

/-- For any valid index into fixedDistLengths, the entry is non-zero. -/
theorem fixedDistLengths_getElem_pos (i : Nat) (h : i < fixedDistLengths.length) :
    fixedDistLengths[i]! ≥ 1 := by
  rw [getElem!_pos fixedDistLengths i h]
  have := fixedDistLengths_entry_bounds (fixedDistLengths[i]) (List.getElem_mem h)
  exact this.1

/-- For any valid index into fixedDistLengths, the entry is ≤ 15. -/
theorem fixedDistLengths_getElem_le (i : Nat) (h : i < fixedDistLengths.length) :
    fixedDistLengths[i]! ≤ 15 := by
  rw [getElem!_pos fixedDistLengths i h]
  have := fixedDistLengths_entry_bounds (fixedDistLengths[i]) (List.getElem_mem h)
  exact this.2

/-! ## encodeLitLen succeeds for matchLZ77 symbols -/

/-- `encodeLitLen` succeeds for literal bytes with fixed Huffman tables. -/
theorem encodeLitLen_literal_isSome (b : UInt8) :
    (encodeLitLen fixedLitLengths fixedDistLengths (.literal b)).isSome = true := by
  simp only [encodeLitLen]
  have hlt : b.toNat < 288 := by have := UInt8.toNat_lt b; omega
  have hsym : b.toNat < fixedLitLengths.length := by rw [fixedLitLengths_length]; exact hlt
  exact encodeSymbol_fixed_isSome fixedLitLengths 15 b.toNat hsym
    (by have := fixedLitLengths_getElem_pos b.toNat hsym; omega)
    (fixedLitLengths_getElem_le b.toNat hsym)

/-- `encodeLitLen` succeeds for endOfBlock with fixed Huffman tables. -/
theorem encodeLitLen_endOfBlock_isSome :
    (encodeLitLen fixedLitLengths fixedDistLengths .endOfBlock).isSome = true := by
  simp only [encodeLitLen]
  have hsym : 256 < fixedLitLengths.length := by rw [fixedLitLengths_length]; omega
  exact encodeSymbol_fixed_isSome fixedLitLengths 15 256 hsym
    (by have := fixedLitLengths_getElem_pos 256 hsym; omega)
    (fixedLitLengths_getElem_le 256 hsym)

/-- Helper: `findLengthCode.go i` succeeds when some entry at index ≥ i covers len. -/
private theorem findLengthCode.go_isSome_of_covered (len i : Nat)
    (hi : i < lengthBase.size)
    (hcov : lengthBase[i] ≤ len)
    (hle : len ≤ 258) :
    (findLengthCode.go len i).isSome = true := by
  unfold findLengthCode.go
  simp only [show ¬(i ≥ lengthBase.size) from by omega, dif_neg, not_false_eq_true]
  by_cases hbucket : (decide (lengthBase[i] ≤ len) && decide (len < (lengthBase[i + 1]?.getD 259))) = true
  · simp [hbucket]
  · simp [hbucket]
    -- Not in this bucket, so len ≥ nextBase
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hbucket
    have hge_next : (lengthBase[i + 1]?.getD 259) ≤ len := by
      by_cases h : lengthBase[i] ≤ len
      · simp [h] at hbucket; omega
      · omega
    -- nextBase = lengthBase[i+1] if i+1 < size, else 259
    have hi1 : i + 1 < lengthBase.size := by
      by_cases h : i + 1 < lengthBase.size
      · exact h
      · exfalso
        -- i is the last entry, nextBase = 259
        have hout : ¬(i + 1 < lengthBase.size) := h
        have : (lengthBase[i + 1]?.getD 259) = 259 := by
          have := getElem?_neg lengthBase (i + 1) (by omega)
          simp [this]
        omega
    have hcov' : lengthBase[i + 1] ≤ len := by
      have : lengthBase[i + 1]? = some lengthBase[i + 1] :=
        getElem?_pos lengthBase (i + 1) hi1
      simp [this] at hge_next
      exact hge_next
    exact findLengthCode.go_isSome_of_covered len (i + 1) hi1 hcov' hle
  termination_by lengthBase.size - i

/-- `findLengthCode` succeeds for lengths 3–258. -/
theorem findLengthCode_isSome (len : Nat) (hge : len ≥ 3) (hle : len ≤ 258) :
    (findLengthCode len).isSome = true := by
  simp only [findLengthCode]
  exact findLengthCode.go_isSome_of_covered len 0
    (by simp [lengthBase]) (by simp [lengthBase]; omega) hle

/-- Helper: `findLengthCode.go` returns indices in [i, size). -/
private theorem findLengthCode.go_idx_bound (len i idx extraN extraV : Nat)
    (h : findLengthCode.go len i = some (idx, extraN, extraV)) :
    i ≤ idx ∧ idx < lengthBase.size := by
  unfold findLengthCode.go at h
  split at h
  · simp at h
  · rename_i hsz; simp at hsz
    by_cases hbucket : (decide (lengthBase[i] ≤ len) && decide (len < (lengthBase[i + 1]?.getD 259))) = true
    · simp [hbucket] at h
      obtain ⟨rfl, _, _⟩ := h
      exact ⟨Nat.le.refl, hsz⟩
    · simp [hbucket] at h
      have := findLengthCode.go_idx_bound len (i + 1) idx extraN extraV h
      exact ⟨by omega, this.2⟩
  termination_by lengthBase.size - i

/-- When `findLengthCode` succeeds, the returned index is < 29. -/
theorem findLengthCode_idx_bound (len idx extraN extraV : Nat)
    (h : findLengthCode len = some (idx, extraN, extraV)) :
    idx < 29 := by
  have := (findLengthCode.go_idx_bound len 0 idx extraN extraV h).2
  simp [lengthBase] at this
  exact this

/-- Helper: `findDistCode.go i` succeeds when distBase[i] ≤ dist ≤ 32768. -/
private theorem findDistCode.go_isSome_of_covered (dist i : Nat)
    (hi : i < distBase.size)
    (hcov : distBase[i] ≤ dist)
    (hle : dist ≤ 32768) :
    (findDistCode.go dist i).isSome = true := by
  unfold findDistCode.go
  simp only [show ¬(i ≥ distBase.size) from by omega, dif_neg, not_false_eq_true]
  by_cases hbucket : (decide (distBase[i] ≤ dist) && decide (dist < (distBase[i + 1]?.getD 32769))) = true
  · simp [hbucket]
  · simp [hbucket]
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hbucket
    have hge_next : (distBase[i + 1]?.getD 32769) ≤ dist := by
      by_cases h : distBase[i] ≤ dist
      · simp [h] at hbucket; omega
      · omega
    have hi1 : i + 1 < distBase.size := by
      by_cases h : i + 1 < distBase.size
      · exact h
      · exfalso
        have := getElem?_neg distBase (i + 1) (by omega)
        simp [this] at hge_next
        omega
    have hcov' : distBase[i + 1] ≤ dist := by
      have : distBase[i + 1]? = some distBase[i + 1] :=
        getElem?_pos distBase (i + 1) hi1
      simp [this] at hge_next
      exact hge_next
    exact findDistCode.go_isSome_of_covered dist (i + 1) hi1 hcov' hle
  termination_by distBase.size - i

/-- `findDistCode` succeeds for distances 1–32768. -/
theorem findDistCode_isSome (dist : Nat) (hge : dist ≥ 1) (hle : dist ≤ 32768) :
    (findDistCode dist).isSome = true := by
  simp only [findDistCode]
  exact findDistCode.go_isSome_of_covered dist 0
    (by simp [distBase]) (by simp [distBase]; omega) hle

/-- Helper: `findDistCode.go` returns codes in [i, size). -/
private theorem findDistCode.go_code_bound (dist i dCode dExtraN dExtraV : Nat)
    (h : findDistCode.go dist i = some (dCode, dExtraN, dExtraV)) :
    i ≤ dCode ∧ dCode < distBase.size := by
  unfold findDistCode.go at h
  split at h
  · simp at h
  · rename_i hsz; simp at hsz
    by_cases hbucket : (decide (distBase[i] ≤ dist) && decide (dist < (distBase[i + 1]?.getD 32769))) = true
    · simp [hbucket] at h
      obtain ⟨rfl, _, _⟩ := h
      exact ⟨Nat.le.refl, hsz⟩
    · simp [hbucket] at h
      have := findDistCode.go_code_bound dist (i + 1) dCode dExtraN dExtraV h
      exact ⟨by omega, this.2⟩
  termination_by distBase.size - i

/-- When `findDistCode` succeeds, the returned code is < 30. -/
theorem findDistCode_code_bound (dist dCode dExtraN dExtraV : Nat)
    (h : findDistCode dist = some (dCode, dExtraN, dExtraV)) :
    dCode < 30 := by
  have := (findDistCode.go_code_bound dist 0 dCode dExtraN dExtraV h).2
  simp [distBase] at this
  exact this

/-- `encodeLitLen` succeeds for references with appropriate bounds. -/
theorem encodeLitLen_reference_isSome (len dist : Nat)
    (hlen_ge : len ≥ 3) (hlen_le : len ≤ 258)
    (hdist_ge : dist ≥ 1) (hdist_le : dist ≤ 32768) :
    (encodeLitLen fixedLitLengths fixedDistLengths
      (.reference len dist)).isSome = true := by
  simp only [encodeLitLen]
  -- findLengthCode succeeds
  have hflc := findLengthCode_isSome len hlen_ge hlen_le
  cases hlc : findLengthCode len with
  | none => simp [hlc] at hflc
  | some p =>
    obtain ⟨idx, extraN, extraV⟩ := p
    have hidx := findLengthCode_idx_bound len idx extraN extraV hlc
    simp only [bind, Option.bind]
    -- encodeSymbol litTable (257 + idx) succeeds
    have hsym : 257 + idx < fixedLitLengths.length := by
      rw [fixedLitLengths_length]; omega
    have hlit := encodeSymbol_fixed_isSome fixedLitLengths 15 (257 + idx) hsym
      (by have := fixedLitLengths_getElem_pos (257 + idx) hsym; omega)
      (fixedLitLengths_getElem_le (257 + idx) hsym)
    cases hls : encodeSymbol
        ((Huffman.Spec.allCodes fixedLitLengths).map fun (s, cw) => (cw, s)) (257 + idx) with
    | none => simp [hls] at hlit
    | some lenBits =>
      simp only [bind, Option.bind]
      -- findDistCode succeeds
      have hfdc := findDistCode_isSome dist hdist_ge hdist_le
      cases hdc : findDistCode dist with
      | none => simp [hdc] at hfdc
      | some q =>
        obtain ⟨dCode, dExtraN, dExtraV⟩ := q
        have hdcode := findDistCode_code_bound dist dCode dExtraN dExtraV hdc
        simp only [bind, Option.bind]
        -- encodeSymbol distTable dCode succeeds
        have hdsym : dCode < fixedDistLengths.length := by
          rw [fixedDistLengths_length]; omega
        have hdist := encodeSymbol_fixed_isSome fixedDistLengths 15 dCode hdsym
          (by have := fixedDistLengths_getElem_pos dCode hdsym; omega)
          (fixedDistLengths_getElem_le dCode hdsym)
        cases hds : encodeSymbol
            ((Huffman.Spec.allCodes fixedDistLengths).map fun (s, cw) => (cw, s)) dCode with
        | none => simp [hds] at hdist
        | some distBits =>
          simp [pure, Pure.pure]

/-- `matchLength` returns at most 258 (the default maxLen). -/
theorem matchLength_le_258 (data : List UInt8) (pos dist : Nat) :
    matchLength data pos dist ≤ 258 := by
  unfold matchLength
  split
  · omega
  · exact (matchLength.go_bounds data pos dist 0 258 (by omega)).2

/-- `encodeSymbols` succeeds when `encodeLitLen` succeeds for each symbol. -/
theorem encodeSymbols_isSome_of_all (litLengths distLengths : List Nat)
    (syms : List LZ77Symbol)
    (h : ∀ s ∈ syms, (encodeLitLen litLengths distLengths s).isSome = true) :
    (encodeSymbols litLengths distLengths syms).isSome = true := by
  induction syms with
  | nil => simp [encodeSymbols]
  | cons s rest ih =>
    simp only [encodeSymbols]
    have hs := h s (List.mem_cons_self ..)
    cases hes : encodeLitLen litLengths distLengths s with
    | none => simp [hes] at hs
    | some bits =>
      simp only [bind, Option.bind]
      have hrest := ih (fun s' hs' => h s' (List.mem_cons_of_mem s hs'))
      cases her : encodeSymbols litLengths distLengths rest with
      | none => simp [her] at hrest
      | some restBits => simp [pure, Pure.pure]

/-! ## RLE encoding of DEFLATE code lengths (RFC 1951 §3.2.7) -/

/-- A code-length entry for DEFLATE dynamic blocks (RFC 1951 §3.2.7).
    Each entry is `(clCode, extraValue)` where:
    - clCode 0–15: literal code length, extraValue = 0
    - clCode 16: repeat previous, extraValue = count − 3 (0–3, 2 bits)
    - clCode 17: repeat zero, extraValue = count − 3 (0–7, 3 bits)
    - clCode 18: repeat zero long, extraValue = count − 11 (0–127, 7 bits) -/
abbrev CLEntry := Nat × Nat

/-- Count consecutive occurrences of `val` at the front of `xs`. -/
def countRun (val : Nat) : List Nat → Nat
  | x :: xs => if x == val then 1 + countRun val xs else 0
  | [] => 0

theorem countRun_le_length (val : Nat) (xs : List Nat) :
    countRun val xs ≤ xs.length := by
  induction xs with
  | nil => simp [countRun]
  | cons x xs ih =>
    simp only [countRun]
    split <;> simp <;> omega

/-- RLE-encode a list of code lengths into CL entries.
    Greedy strategy: use the longest possible run at each position.
    For runs of zeros: use codes 17 or 18.
    For runs of the same non-zero value: emit literal then code 16. -/
def rlEncodeLengths (lengths : List Nat) : List CLEntry :=
  go lengths
where
  go : List Nat → List CLEntry
    | [] => []
    | x :: xs =>
      if x == 0 then
        let runLen := 1 + countRun 0 xs
        if runLen >= 11 then
          let take := min runLen 138
          (18, take - 11) :: go (xs.drop (take - 1))
        else if runLen >= 3 then
          (17, runLen - 3) :: go (xs.drop (runLen - 1))
        else
          -- 1 or 2 zeros: emit as literals
          (0, 0) :: go xs
      else
        let runLen := countRun x xs
        if runLen >= 3 then
          let take := min runLen 6
          (x, 0) :: (16, take - 3) :: go (xs.drop take)
        else
          (x, 0) :: go xs
  termination_by xs => xs.length
  decreasing_by
    all_goals simp_all [List.length_drop]
    all_goals have := countRun_le_length 0 xs; omega

/-- Decode a list of CL entries back into code lengths.
    This is the pure (non-Huffman) inverse of `rlEncodeLengths`.
    Code 16 requires a previous value, so we use an accumulator. -/
def rlDecodeLengths (entries : List CLEntry) : Option (List Nat) :=
  go entries []
where
  go : List CLEntry → List Nat → Option (List Nat)
    | [], acc => some acc
    | (code, extra) :: rest, acc =>
      if code ≤ 15 then
        go rest (acc ++ [code])
      else if code == 16 then do
        guard (acc.length > 0)
        let prev := acc.getLast!
        go rest (acc ++ List.replicate (extra + 3) prev)
      else if code == 17 then
        go rest (acc ++ List.replicate (extra + 3) 0)
      else if code == 18 then
        go rest (acc ++ List.replicate (extra + 11) 0)
      else none

theorem countRun_take (val : Nat) (xs : List Nat) :
    xs.take (countRun val xs) = List.replicate (countRun val xs) val := by
  induction xs with
  | nil => simp [countRun]
  | cons x xs ih =>
    simp only [countRun]
    split
    · rename_i heq; simp only [beq_iff_eq] at heq; subst heq
      show (x :: xs).take (1 + countRun x xs) = List.replicate (1 + countRun x xs) x
      rw [show 1 + countRun x xs = (countRun x xs) + 1 from by omega]
      rw [List.take_succ_cons, List.replicate_succ]
      exact congrArg (x :: ·) ih
    · show (x :: xs).take 0 = List.replicate 0 val
      simp

/-- Taking at most `countRun val xs` elements from `xs` gives all `val`s. -/
theorem take_countRun_eq_replicate (val : Nat) (xs : List Nat) (n : Nat) (hn : n ≤ countRun val xs) :
    xs.take n = List.replicate n val := by
  induction xs generalizing n with
  | nil => simp [countRun] at hn; simp [hn]
  | cons x xs ih =>
    simp only [countRun] at hn
    split at hn
    · rename_i heq; simp only [beq_iff_eq] at heq; subst heq
      cases n with
      | zero => simp
      | succ n =>
        simp only [List.take_succ_cons, List.replicate_succ]
        exact congrArg (x :: ·) (ih n (by omega))
    · have : n = 0 := by omega
      subst this; simp

private theorem drop_subset_valid {xs : List Nat} {n : Nat}
    (hvalid : ∀ y ∈ xs, y ≤ 15) : ∀ y ∈ xs.drop n, y ≤ 15 :=
  fun y hy => hvalid y (List.drop_subset n xs hy)

-- Step lemmas for rlDecodeLengths.go on each code type
private theorem rlDecode_go_literal (code : Nat) (extra : Nat)
    (rest : List CLEntry) (acc : List Nat) (hle : code ≤ 15) :
    rlDecodeLengths.go ((code, extra) :: rest) acc =
      rlDecodeLengths.go rest (acc ++ [code]) := by
  simp only [rlDecodeLengths.go, hle, ↓reduceIte]

private theorem rlDecode_go_code17 (extra : Nat)
    (rest : List CLEntry) (acc : List Nat) :
    rlDecodeLengths.go ((17, extra) :: rest) acc =
      rlDecodeLengths.go rest (acc ++ List.replicate (extra + 3) 0) := by
  simp [rlDecodeLengths.go]

private theorem rlDecode_go_code18 (extra : Nat)
    (rest : List CLEntry) (acc : List Nat) :
    rlDecodeLengths.go ((18, extra) :: rest) acc =
      rlDecodeLengths.go rest (acc ++ List.replicate (extra + 11) 0) := by
  simp [rlDecodeLengths.go]

private theorem rlDecode_go_code16 (extra : Nat)
    (rest : List CLEntry) (acc : List Nat) (hne : acc.length > 0) :
    rlDecodeLengths.go ((16, extra) :: rest) acc =
      rlDecodeLengths.go rest (acc ++ List.replicate (extra + 3) acc.getLast!) := by
  simp [rlDecodeLengths.go, hne, guard, pure, bind]

/-- Replicate zeros plus the rest of the list equals the original cons-zero list. -/
private theorem replicate_drop_eq_cons_zero (xs : List Nat) (n : Nat)
    (hn1 : n ≥ 1) (hn : n ≤ 1 + countRun 0 xs) :
    List.replicate n 0 ++ xs.drop (n - 1) = 0 :: xs := by
  rw [← take_countRun_eq_replicate 0 (0 :: xs) n (by simp [countRun]; omega)]
  have hdrop : xs.drop (n - 1) = (0 :: xs).drop n := by
    cases n with
    | zero => omega
    | succ k => simp [List.drop_succ_cons]
  rw [hdrop, List.take_append_drop]

/-- Singleton plus replicate plus drop equals the original cons list. -/
private theorem singleton_replicate_drop_eq_cons (x : Nat) (xs : List Nat) (m : Nat)
    (hm : m ≤ countRun x xs) :
    [x] ++ List.replicate m x ++ xs.drop m = x :: xs := by
  rw [← take_countRun_eq_replicate x xs m hm]
  simp [List.take_append_drop]

/-- Generalized roundtrip: decoding an encoded list recovers the accumulator plus the list. -/
theorem rlDecodeLengths_go_rlEncodeLengths_go (lengths : List Nat) (acc : List Nat)
    (hvalid : ∀ x ∈ lengths, x ≤ 15) :
    rlDecodeLengths.go (rlEncodeLengths.go lengths) acc = some (acc ++ lengths) := by
  match lengths with
  | [] => simp [rlEncodeLengths.go, rlDecodeLengths.go]
  | x :: xs =>
    have hx_valid : x ≤ 15 := hvalid x (.head ..)
    have hxs_valid : ∀ y ∈ xs, y ≤ 15 := fun y hy => hvalid y (List.mem_cons_of_mem x hy)
    have hcr0 := countRun_le_length 0 xs
    have hcrx := countRun_le_length x xs
    rw [rlEncodeLengths.go]
    by_cases hx0 : x = 0
    · subst hx0
      simp only [beq_self_eq_true, ↓reduceIte]
      by_cases hge11 : 1 + countRun 0 xs >= 11
      · -- code 18: repeat zero 11-138
        rw [if_pos (by omega : 1 + countRun 0 xs ≥ 11), rlDecode_go_code18]
        rw [show min (1 + countRun 0 xs) 138 - 11 + 11 = min (1 + countRun 0 xs) 138 from by omega]
        rw [rlDecodeLengths_go_rlEncodeLengths_go _ _ (drop_subset_valid hxs_valid)]
        simp only [List.append_assoc]
        exact congrArg (fun z => some (acc ++ z))
          (replicate_drop_eq_cons_zero xs _ (by omega) (by omega))
      · rw [if_neg (by omega)]
        by_cases hge3 : 1 + countRun 0 xs >= 3
        · -- code 17: repeat zero 3-10
          rw [if_pos (by omega : 1 + countRun 0 xs ≥ 3), rlDecode_go_code17]
          rw [show 1 + countRun 0 xs - 3 + 3 = 1 + countRun 0 xs from by omega]
          rw [rlDecodeLengths_go_rlEncodeLengths_go _ _ (drop_subset_valid hxs_valid)]
          simp only [List.append_assoc]
          exact congrArg (fun z => some (acc ++ z))
            (replicate_drop_eq_cons_zero xs _ (by omega) (by omega))
        · -- literal 0
          rw [if_neg (by omega), rlDecode_go_literal 0 0 _ _ (by omega)]
          rw [rlDecodeLengths_go_rlEncodeLengths_go xs (acc ++ [0]) hxs_valid]
          simp [List.append_assoc]
    · simp only [show (x == 0) = false from by cases h : x == 0 <;> simp_all [beq_iff_eq],
                  Bool.false_eq_true, ↓reduceIte]
      by_cases hge3 : countRun x xs >= 3
      · -- literal + code 16: repeat previous 3-6
        rw [if_pos (by omega : countRun x xs ≥ 3)]
        rw [rlDecode_go_literal x 0 _ _ hx_valid, rlDecode_go_code16 _ _ _ (by simp)]
        rw [show (acc ++ [x]).getLast! = x from by simp]
        rw [show min (countRun x xs) 6 - 3 + 3 = min (countRun x xs) 6 from by omega]
        rw [rlDecodeLengths_go_rlEncodeLengths_go _ _ (drop_subset_valid hxs_valid)]
        simp only [List.append_assoc]
        exact congrArg (fun z => some (acc ++ z))
          (singleton_replicate_drop_eq_cons x xs _ (Nat.min_le_left _ _))
      · -- literal (no repeat)
        rw [if_neg (by omega), rlDecode_go_literal x 0 _ _ hx_valid]
        rw [rlDecodeLengths_go_rlEncodeLengths_go xs (acc ++ [x]) hxs_valid]
        simp [List.append_assoc]
termination_by lengths.length
decreasing_by all_goals simp_all [List.length_drop] <;> omega

/-- Encoding then decoding code lengths recovers the original list. -/
theorem rlDecodeLengths_rlEncodeLengths (lengths : List Nat)
    (hvalid : ∀ x ∈ lengths, x ≤ 15) :
    rlDecodeLengths (rlEncodeLengths lengths) = some lengths := by
  simp only [rlDecodeLengths, rlEncodeLengths]
  have := rlDecodeLengths_go_rlEncodeLengths_go lengths [] hvalid
  simp at this
  exact this

/-- Every entry produced by `rlEncodeLengths.go` satisfies the CL code constraints. -/
theorem rlEncodeLengths_go_valid (lengths : List Nat)
    (hvalid : ∀ x ∈ lengths, x ≤ 15) :
    ∀ entry ∈ rlEncodeLengths.go lengths,
      (entry.1 ≤ 15 ∧ entry.2 = 0) ∨
      (entry.1 = 16 ∧ entry.2 ≤ 3) ∨
      (entry.1 = 17 ∧ entry.2 ≤ 7) ∨
      (entry.1 = 18 ∧ entry.2 ≤ 127) := by
  match lengths with
  | [] => simp [rlEncodeLengths.go]
  | x :: xs =>
    have hx_valid : x ≤ 15 := hvalid x (.head ..)
    have hxs_valid : ∀ y ∈ xs, y ≤ 15 := fun y hy => hvalid y (List.mem_cons_of_mem x hy)
    rw [rlEncodeLengths.go]
    by_cases hx0 : x = 0
    · subst hx0
      simp only [beq_self_eq_true, ↓reduceIte]
      by_cases hge11 : 1 + countRun 0 xs ≥ 11
      · rw [if_pos (by omega : 1 + countRun 0 xs ≥ 11)]
        intro entry hmem
        simp only [List.mem_cons] at hmem
        cases hmem with
        | inl h => subst h; right; right; right; constructor <;> omega
        | inr h =>
          exact rlEncodeLengths_go_valid _ (drop_subset_valid hxs_valid) entry h
      · rw [if_neg (by omega)]
        by_cases hge3 : 1 + countRun 0 xs ≥ 3
        · rw [if_pos (by omega : 1 + countRun 0 xs ≥ 3)]
          intro entry hmem
          simp only [List.mem_cons] at hmem
          cases hmem with
          | inl h => subst h; right; right; left; constructor <;> omega
          | inr h =>
            exact rlEncodeLengths_go_valid _ (drop_subset_valid hxs_valid) entry h
        · rw [if_neg (by omega)]
          intro entry hmem
          simp only [List.mem_cons] at hmem
          cases hmem with
          | inl h => subst h; left; exact ⟨by omega, rfl⟩
          | inr h =>
            exact rlEncodeLengths_go_valid _ hxs_valid entry h
    · simp only [show (x == 0) = false from by cases h : x == 0 <;> simp_all [beq_iff_eq],
                  Bool.false_eq_true, ↓reduceIte]
      by_cases hge3 : countRun x xs ≥ 3
      · rw [if_pos (by omega : countRun x xs ≥ 3)]
        intro entry hmem
        simp only [List.mem_cons] at hmem
        cases hmem with
        | inl h => subst h; left; exact ⟨hx_valid, rfl⟩
        | inr h =>
          cases h with
          | inl h => subst h; right; left; constructor <;> omega
          | inr h =>
            exact rlEncodeLengths_go_valid _ (drop_subset_valid hxs_valid) entry h
      · rw [if_neg (by omega)]
        intro entry hmem
        simp only [List.mem_cons] at hmem
        cases hmem with
        | inl h => subst h; left; exact ⟨hx_valid, rfl⟩
        | inr h =>
          exact rlEncodeLengths_go_valid _ hxs_valid entry h
termination_by lengths.length
decreasing_by all_goals simp_all [List.length_drop] <;> omega

/-- Every entry produced by `rlEncodeLengths` satisfies the CL code constraints:
    codes 0-15 have extra = 0, code 16 has extra ≤ 3, code 17 has extra ≤ 7,
    code 18 has extra ≤ 127. -/
theorem rlEncodeLengths_valid (lengths : List Nat)
    (hvalid : ∀ x ∈ lengths, x ≤ 15) :
    ∀ entry ∈ rlEncodeLengths lengths,
      (entry.1 ≤ 15 ∧ entry.2 = 0) ∨
      (entry.1 = 16 ∧ entry.2 ≤ 3) ∨
      (entry.1 = 17 ∧ entry.2 ≤ 7) ∨
      (entry.1 = 18 ∧ entry.2 ≤ 127) := by
  exact rlEncodeLengths_go_valid lengths hvalid

end Deflate.Spec
