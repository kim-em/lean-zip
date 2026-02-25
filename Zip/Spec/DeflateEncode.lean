import Zip.Spec.Deflate
import Zip.Spec.HuffmanEncode

/-!
# DEFLATE Encoding Specification

Core Huffman symbol encoding functions and roundtrip theorems for DEFLATE.
- Length/distance table lookup (`findLengthCode`, `findDistCode`)
- Symbol encoding (`encodeSymbol`, `encodeLitLen`, `encodeSymbols`)
- Encoding roundtrip theorems (`encodeLitLen_decodeLitLen`, `encodeSymbols_decodeSymbols`)
- Fixed Huffman block encoder (`encodeFixed`) and decode roundtrip

Encoding success properties are in `Zip.Spec.DeflateEncodeProps`.
Dynamic block header encoding is in `Zip.Spec.DeflateEncodeDynamic`.
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

set_option linter.unusedSimpArgs false in
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

set_option linter.unusedSimpArgs false in
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

set_option linter.unusedSimpArgs false in
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

set_option linter.unusedSimpArgs false in
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

/-- Upper bound from `findLengthCode`: `len < lengthBase[idx + 1]!` when
    `idx` is not the last entry. -/
theorem findLengthCode_upper (len idx extraN extraV : Nat)
    (h : findLengthCode len = some (idx, extraN, extraV))
    (hidx : idx + 1 < 29) :
    len < lengthBase[idx + 1]! := by
  have hgo := findLengthCode_go_spec len 0 idx extraN extraV h
  have hsize : idx + 1 < lengthBase.size := by simp [lengthBase]; omega
  have := hgo.2.2.2
  rw [getElem?_pos lengthBase (idx + 1) hsize] at this
  simp only [Option.getD] at this
  rw [getElem!_pos lengthBase (idx + 1) hsize]
  exact this

/-- Upper bound from `findDistCode`: `dist < distBase[idx + 1]!` when
    `idx` is not the last entry. -/
theorem findDistCode_upper (dist idx extraN extraV : Nat)
    (h : findDistCode dist = some (idx, extraN, extraV))
    (hidx : idx + 1 < 30) :
    dist < distBase[idx + 1]! := by
  have hgo := findDistCode_go_spec dist 0 idx extraN extraV h
  have hsize : idx + 1 < distBase.size := by simp [distBase]; omega
  have := hgo.2.2.2
  rw [getElem?_pos distBase (idx + 1) hsize] at this
  simp only [Option.getD] at this
  rw [getElem!_pos distBase (idx + 1) hsize]
  exact this

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
          | literal _ | reference _ _ =>
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

/-- Encoding with fixed Huffman then decoding recovers the original data,
    even when trailing bits are appended. -/
theorem encodeFixed_decode_append (syms : List LZ77Symbol) (data : List UInt8)
    (bits rest : List Bool)
    (henc : encodeSymbols fixedLitLengths fixedDistLengths syms = some bits)
    (hresolve : resolveLZ77 syms [] = some data)
    (hfuel : 1000000000 ≥ syms.length)
    (hvalid : ValidSymbolList syms) :
    decode ([true, true, false] ++ bits ++ rest) = some data := by
  show decode.go ([true, true, false] ++ bits ++ rest) [] 10001 = some data
  unfold decode.go
  simp only [List.cons_append, readBitsLSB_1_true, bind, Option.bind]
  simp only [readBitsLSB_2_true_false]
  have hdec : decodeSymbols fixedLitLengths fixedDistLengths (bits ++ rest)
      1000000000 = some (syms, rest) :=
    encodeSymbols_decodeSymbols fixedLitLengths fixedDistLengths syms bits rest
      1000000000 henc fixedLitLengths_valid fixedDistLengths_valid hfuel hvalid
  simp only [List.nil_append]
  rw [hdec]
  simp only [hresolve]
  simp [pure, Pure.pure]

/-- Encoding with fixed Huffman then decoding recovers the original data. -/
theorem encodeFixed_decode (syms : List LZ77Symbol) (data : List UInt8)
    (bits : List Bool)
    (henc : encodeSymbols fixedLitLengths fixedDistLengths syms = some bits)
    (hresolve : resolveLZ77 syms [] = some data)
    (hfuel : 1000000000 ≥ syms.length)
    (hvalid : ValidSymbolList syms) :
    decode ([true, true, false] ++ bits) = some data := by
  have := encodeFixed_decode_append syms data bits [] henc hresolve hfuel hvalid
  rwa [List.append_nil] at this

private theorem readBitsLSB_2_false_true (rest : List Bool) :
    readBitsLSB 2 (false :: true :: rest) = some (2, rest) := by
  simp [readBitsLSB]

/-- Encoding with dynamic Huffman then decoding recovers the original data,
    even when trailing bits are appended. The header must have been previously
    decoded via `decodeDynamicTables`. -/
theorem encodeDynamic_decode_append (syms : List LZ77Symbol) (data : List UInt8)
    (litLens distLens : List Nat)
    (headerBits symBits rest : List Bool)
    (hv_lit : Huffman.Spec.ValidLengths litLens 15)
    (hv_dist : Huffman.Spec.ValidLengths distLens 15)
    (hheader : decodeDynamicTables (headerBits ++ symBits ++ rest) =
        some (litLens, distLens, symBits ++ rest))
    (henc : encodeSymbols litLens distLens syms = some symBits)
    (hresolve : resolveLZ77 syms [] = some data)
    (hfuel : 1000000000 ≥ syms.length)
    (hvalid : ValidSymbolList syms) :
    decode ([true, false, true] ++ headerBits ++ symBits ++ rest) = some data := by
  show decode.go ([true, false, true] ++ headerBits ++ symBits ++ rest) [] 10001 = some data
  unfold decode.go
  simp only [List.cons_append, readBitsLSB_1_true, bind, Option.bind]
  simp only [readBitsLSB_2_false_true]
  -- Now in btype = 2 (dynamic Huffman) branch
  simp only [List.nil_append]
  rw [hheader]
  set_option linter.unusedSimpArgs false in
  simp only [bind, Option.bind]
  have hdec : decodeSymbols litLens distLens (symBits ++ rest)
      1000000000 = some (syms, rest) :=
    encodeSymbols_decodeSymbols litLens distLens syms symBits rest
      1000000000 henc hv_lit hv_dist hfuel hvalid
  rw [hdec]
  simp only [hresolve]
  simp [pure, Pure.pure]

end Deflate.Spec
