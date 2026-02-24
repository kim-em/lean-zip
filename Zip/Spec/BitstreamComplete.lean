import Zip.Spec.BitstreamCorrect

/-!
# Bitstream Completeness (Reverse Direction)

Completeness theorems for `BitReader` operations: if the spec-level
`readBitsLSB` (or `readNBytes`) succeeds, then the corresponding native
`BitReader` operation also succeeds with the same value.

These are the reverses of the forward-direction correspondence theorems
in `BitstreamCorrect.lean`. Together they establish full equivalence
between the native byte-level reader and the spec-level bit list model.
-/

namespace Deflate.Correctness

/-! ### Reverse direction (completeness): spec success → native success -/

/-- If `br.toBits` is non-empty and `bitOff < 8`, then `pos < data.size`. -/
protected theorem toBits_nonempty_pos (br : Zip.Native.BitReader)
    (hwf : br.bitOff < 8) (h : br.toBits.length > 0) :
    br.pos < br.data.size := by
  rw [Deflate.Correctness.toBits_length] at h; omega

/-- **Completeness for `readBit`**: if `br.toBits` starts with `b :: rest`,
    then `readBit` succeeds and the resulting reader corresponds to `rest`. -/
protected theorem readBit_complete (br : Zip.Native.BitReader) (b : Bool) (rest : List Bool)
    (hwf : br.bitOff < 8)
    (hbits : br.toBits = b :: rest) :
    ∃ br', br.readBit = .ok ((if b then 1 else 0), br') ∧
      br'.toBits = rest ∧
      br'.bitOff < 8 ∧
      (br'.bitOff = 0 ∨ br'.pos < br'.data.size) := by
  -- toBits non-empty → pos < data.size
  have hpos : br.pos < br.data.size := by
    apply Deflate.Correctness.toBits_nonempty_pos br hwf
    rw [hbits]; simp
  -- Get the structural fact about toBits from bytesToBits_drop_testBit
  obtain ⟨rest', hrest'⟩ := Deflate.Correctness.bytesToBits_drop_testBit br.data br.pos br.bitOff hpos hwf
  -- Match hbits against hrest' to extract b and rest
  simp only [Zip.Native.BitReader.toBits] at hbits
  rw [hrest'] at hbits
  have hhead : b = br.data[br.pos].toNat.testBit br.bitOff :=
    (List.cons.inj hbits).1.symm
  have hrest_eq : rest = rest' := (List.cons.inj hbits).2.symm
  have hrest'_eq : rest' =
      (Deflate.Spec.bytesToBits br.data).drop (br.pos * 8 + br.bitOff + 1) :=
    Deflate.Correctness.list_drop_cons_tail hrest'
  -- Unfold readBit — pos < data.size so the error branch is impossible
  have hge : ¬(br.pos ≥ br.data.size) := by omega
  simp only [Zip.Native.BitReader.readBit, hge, ↓reduceIte]
  -- The bit value matches
  have hbit_val : ((br.data[br.pos]!.toUInt32 >>> br.bitOff.toUInt32) &&& 1) =
      if b then 1 else 0 := by
    have : br.data[br.pos]! = br.data[br.pos] := by simp [hpos]
    rw [this, hhead, Deflate.Correctness.uint32_bit_eq_testBit br.data[br.pos] br.bitOff hwf]
  -- Split on bitOff + 1 ≥ 8
  by_cases hoff : br.bitOff + 1 ≥ 8
  · -- bitOff + 1 ≥ 8 → advance to next byte
    have hoff' : br.bitOff + 1 ≥ 8 := hoff
    simp only [hoff', ↓reduceIte]
    exact ⟨⟨br.data, br.pos + 1, 0⟩, by rw [hbit_val], by
      rw [hrest_eq, hrest'_eq]
      simp only [Zip.Native.BitReader.toBits, Nat.add_zero]
      congr 1; omega, by simp, Or.inl rfl⟩
  · -- bitOff + 1 < 8 → stay in same byte
    have hoff' : ¬(br.bitOff + 1 ≥ 8) := hoff
    simp only [hoff', ↓reduceIte]
    exact ⟨⟨br.data, br.pos, br.bitOff + 1⟩, by rw [hbit_val], by
      rw [hrest_eq, hrest'_eq]; simp [Zip.Native.BitReader.toBits]; omega,
      by show br.bitOff + 1 < 8; omega, Or.inr hpos⟩

/-- Generalized loop invariant for `readBits.go` completeness (reverse direction). -/
protected theorem readBits_go_complete (br : Zip.Native.BitReader) (acc : UInt32)
    (shift k : Nat) (specVal : Nat) (rest : List Bool)
    (hwf : br.bitOff < 8)
    (hpos : br.bitOff = 0 ∨ br.pos < br.data.size)
    (hsk : shift + k ≤ 32) (hacc : acc.toNat < 2 ^ shift)
    (hbound : specVal < 2 ^ k)
    (hspec : Deflate.Spec.readBitsLSB k br.toBits = some (specVal, rest)) :
    ∃ result br', Zip.Native.BitReader.readBits.go br acc shift k = .ok (result, br') ∧
      result.toNat = acc.toNat + specVal * 2 ^ shift ∧
      br'.toBits = rest ∧
      br'.bitOff < 8 ∧
      (br'.bitOff = 0 ∨ br'.pos < br'.data.size) := by
  induction k generalizing br acc shift specVal with
  | zero =>
    simp only [Deflate.Spec.readBitsLSB] at hspec
    obtain ⟨rfl, rfl⟩ := Option.some.inj hspec
    simp only [Zip.Native.BitReader.readBits.go]
    exact ⟨acc, br, rfl, by simp, rfl, hwf, hpos⟩
  | succ k ih =>
    -- Decompose readBitsLSB (k+1) — need to case-split on br.toBits first
    cases hbits : br.toBits with
    | nil => simp [Deflate.Spec.readBitsLSB, hbits] at hspec
    | cons b tail =>
      simp only [hbits, Deflate.Spec.readBitsLSB, bind, Option.bind] at hspec
      -- readBitsLSB k tail = some (v, rest) with specVal = (if b then 1 else 0) + v * 2
      cases hk : Deflate.Spec.readBitsLSB k tail with
      | none => simp [hk] at hspec
      | some p =>
        obtain ⟨v, rest'⟩ := p
        rw [hk] at hspec
        simp only [pure, Pure.pure, Option.some.injEq, Prod.mk.injEq] at hspec
        obtain ⟨hval, hrst⟩ := hspec
        -- Apply readBit_complete
        obtain ⟨br₁, hrd, hbr1_bits, hwf₁, hpos₁⟩ :=
          Deflate.Correctness.readBit_complete br b tail hwf hbits
        -- bit is 0 or 1
        have hbit : (if b then (1 : UInt32) else 0) = 0 ∨
            (if b then (1 : UInt32) else 0) = 1 := by cases b <;> simp
        have hshift : shift < 32 := by omega
        have hacc' := Deflate.Correctness.acc_or_shift_bound acc (if b then 1 else 0) shift hacc hbit hshift
        -- Bound on v
        have hv_bound : v < 2 ^ k := by
          have : (if b then 1 else 0) + v * 2 = specVal := hval
          cases b <;> simp at this <;> omega
        -- Apply IH
        rw [← hbr1_bits] at hk
        rw [hrst] at hk
        obtain ⟨result, br', hgo, hresult, hbr'_bits, hwf', hpos'⟩ := ih br₁
          (acc ||| ((if b then 1 else 0) <<< shift.toUInt32))
          (shift + 1) v hwf₁ hpos₁ (by omega) hacc' hv_bound hk
        -- Chain readBit and readBits.go
        refine ⟨result, br', ?_, ?_, hbr'_bits, hwf', hpos'⟩
        · -- readBits.go br acc shift (k+1) unfolds to readBit then readBits.go
          simp only [Zip.Native.BitReader.readBits.go, bind, Except.bind, hrd]
          exact hgo
        · -- result.toNat = acc.toNat + specVal * 2^shift
          rw [hresult, Deflate.Correctness.acc_or_shift_toNat acc (if b then 1 else 0) shift hacc hbit hshift,
              ← hval, Nat.pow_succ]
          cases b <;> simp [UInt32.toNat_zero, UInt32.toNat_one] <;> grind

/-- **Completeness for `readBits`**: if the spec-level `readBitsLSB n` succeeds
    on the bit list corresponding to a `BitReader`, then the native `readBits n`
    also succeeds, producing the same value and a reader whose bit list matches
    the spec remainder.

    This is the reverse of `readBits_toBits`.

    Preconditions mirror `readBits_toBits`:
    - `hwf`: the bit offset is well-formed (`bitOff < 8`)
    - `hpos`: the reader is within bounds when `bitOff > 0`
    - `hn`: `n ≤ 32` (UInt32 shift correctness) -/
theorem readBits_complete (br : Zip.Native.BitReader) (n val : Nat) (rest : List Bool)
    (hwf : br.bitOff < 8)
    (hpos : br.bitOff = 0 ∨ br.pos < br.data.size)
    (hn : n ≤ 32)
    (hbound : val < 2 ^ n)
    (hspec : Deflate.Spec.readBitsLSB n br.toBits = some (val, rest)) :
    ∃ br', br.readBits n = .ok (val.toUInt32, br') ∧
      br'.toBits = rest ∧
      br'.bitOff < 8 ∧
      (br'.bitOff = 0 ∨ br'.pos < br'.data.size) := by
  -- readBits = readBits.go br 0 0 n
  simp only [Zip.Native.BitReader.readBits]
  obtain ⟨result, br', hgo, hresult, hbits, hwf', hpos'⟩ :=
    Deflate.Correctness.readBits_go_complete br 0 0 n val rest hwf hpos (by omega) (by simp) hbound hspec
  refine ⟨br', ?_, hbits, hwf', hpos'⟩
  -- result.toNat = 0 + val * 2^0 = val, so result = val.toUInt32
  simp at hresult
  have hlt : val < UInt32.size :=
    Nat.lt_of_lt_of_le hbound (Nat.pow_le_pow_right (by omega) hn)
  have : result = val.toUInt32 :=
    UInt32.toNat_inj.mp (by rw [hresult]; simp [Nat.toUInt32, Nat.mod_eq_of_lt hlt])
  rw [this] at hgo
  exact hgo

/-- **Completeness for `readUInt16LE`**: if the spec reads 16 bits from
    an aligned position, the native `readUInt16LE` succeeds with the same value. -/
theorem readUInt16LE_complete (br : Zip.Native.BitReader) (val : Nat) (rest : List Bool)
    (hwf : br.bitOff < 8)
    (hpos : br.bitOff = 0 ∨ br.pos < br.data.size)
    (hbound : val < 2 ^ 16)
    (hspec : Deflate.Spec.readBitsLSB 16 (Deflate.Spec.alignToByte br.toBits) =
        some (val, rest)) :
    ∃ br', br.readUInt16LE = .ok (val.toUInt16, br') ∧
      br'.toBits = rest ∧
      br'.bitOff = 0 ∧
      (br'.bitOff = 0 ∨ br'.pos < br'.data.size) := by
  -- Rewrite spec hypothesis to use br.alignToByte.toBits
  have halign : br.alignToByte.toBits = Deflate.Spec.alignToByte br.toBits :=
    alignToByte_toBits br hwf hpos
  have hoff : br.alignToByte.bitOff = 0 := alignToByte_wf br
  rw [← halign] at hspec
  -- From readBitsLSB 16 success, derive that aligned reader has ≥ 16 bits = 2 bytes
  have hlen := Deflate.Spec.readBitsLSB_some_length hspec
  have hbits_len : br.alignToByte.toBits.length ≥ 16 := by omega
  rw [Deflate.Correctness.toBits_length] at hbits_len
  have hle : br.alignToByte.pos + 2 ≤ br.alignToByte.data.size := by omega
  -- Split 16-bit read into two 8-bit reads
  rw [show (16 : Nat) = 8 + 8 from rfl, Deflate.Correctness.readBitsLSB_split] at hspec
  -- First byte read
  have hpos0 : br.alignToByte.pos < br.alignToByte.data.size := by omega
  rw [toBits_readBitsLSB_byte br.alignToByte hoff hpos0] at hspec
  simp only [Option.bind] at hspec
  -- Second byte read
  have hpos1 : br.alignToByte.pos + 1 < br.alignToByte.data.size := by omega
  rw [toBits_readBitsLSB_byte ⟨br.alignToByte.data, br.alignToByte.pos + 1, 0⟩ rfl hpos1] at hspec
  simp only [Option.some.injEq, Prod.mk.injEq] at hspec
  obtain ⟨hval_eq, hrest_eq⟩ := hspec
  -- Unfold readUInt16LE: aligns, bounds check passes
  have hbound_check : ¬(br.alignToByte.pos + 2 > br.alignToByte.data.size) := by omega
  have hget0 : br.alignToByte.data[br.alignToByte.pos]! = br.alignToByte.data[br.alignToByte.pos] :=
    by simp [hpos0]
  have hget1 : br.alignToByte.data[br.alignToByte.pos + 1]! = br.alignToByte.data[br.alignToByte.pos + 1] :=
    by simp [hpos1]
  -- Value: lo ||| (hi <<< 8) = val.toUInt16
  have hlo : br.alignToByte.data[br.alignToByte.pos].toNat < 2 ^ 8 :=
    br.alignToByte.data[br.alignToByte.pos].toBitVec.isLt
  have hhi : br.alignToByte.data[br.alignToByte.pos + 1].toNat < 2 ^ 8 :=
    br.alignToByte.data[br.alignToByte.pos + 1].toBitVec.isLt
  have hval_native : br.alignToByte.data[br.alignToByte.pos]!.toUInt16 |||
      (br.alignToByte.data[br.alignToByte.pos + 1]!.toUInt16 <<< 8) = val.toUInt16 := by
    rw [hget0, hget1]
    -- Goal: lo.toUInt16 ||| hi.toUInt16 <<< 8 = val.toUInt16
    -- Strategy: show both have the same .toNat
    have hval_lo_hi : val = br.alignToByte.data[br.alignToByte.pos].toNat +
        br.alignToByte.data[br.alignToByte.pos + 1].toNat * 2 ^ 8 := hval_eq.symm
    apply UInt16.toNat_inj.mp
    simp only [UInt16.toNat_or, UInt16.toNat_shiftLeft, UInt8.toNat_toUInt16,
      show (8 : UInt16).toNat % 16 = 8 from rfl, Nat.shiftLeft_eq]
    -- Goal: (lo ||| (hi * 2^8 % 65536)) % 65536 = val % 65536
    have hhi_shift : br.alignToByte.data[br.alignToByte.pos + 1].toNat * 2 ^ 8 < 65536 := by omega
    rw [Nat.mod_eq_of_lt hhi_shift]
    -- val.toUInt16.toNat = val since val < 2^16
    rw [show val.toUInt16.toNat = val from by
      simp [Nat.toUInt16, Nat.mod_eq_of_lt hbound]]
    -- Goal: lo ||| hi * 2^8 = val
    -- Use Nat.or_comm then shiftLeft_add_eq_or_of_lt (reversed) to convert ||| to +
    rw [Nat.or_comm, ← Nat.shiftLeft_eq, ← Nat.shiftLeft_add_eq_or_of_lt hlo, Nat.shiftLeft_eq]
    omega
  -- Construct the result
  refine ⟨{ br.alignToByte with pos := br.alignToByte.pos + 2 }, ?_, ?_, alignToByte_wf br, Or.inl (alignToByte_wf br)⟩
  · -- readUInt16LE succeeds with the right value
    simp only [Zip.Native.BitReader.readUInt16LE, hbound_check, ↓reduceIte, hval_native]
  · -- br'.toBits = rest
    rw [← hrest_eq]
    simp only [Zip.Native.BitReader.toBits, hoff, Nat.add_zero]
    done

/-- `readNBytes n` success implies the bit list has at least `n * 8` bits. -/
protected theorem readNBytes_some_length {n : Nat} {bits : List Bool} {acc : List UInt8}
    {bytes : List UInt8} {rest : List Bool}
    (h : Deflate.Spec.decodeStored.readNBytes n bits acc = some (bytes, rest)) :
    bits.length ≥ n * 8 := by
  induction n generalizing bits acc with
  | zero => omega
  | succ k ih =>
    simp only [Deflate.Spec.decodeStored.readNBytes] at h
    cases hrd : Deflate.Spec.readBitsLSB 8 bits with
    | none => simp [hrd] at h
    | some p =>
      obtain ⟨v, bits'⟩ := p
      simp only [hrd, bind, Option.bind] at h
      have hlen := Deflate.Spec.readBitsLSB_some_length hrd
      have := ih h
      omega

/-- `readNBytes n bits acc = some (bytes, rest)` implies `bytes.length = acc.length + n`. -/
theorem readNBytes_output_length {n : Nat} {bits : List Bool} {acc : List UInt8}
    {bytes : List UInt8} {rest : List Bool}
    (h : Deflate.Spec.decodeStored.readNBytes n bits acc = some (bytes, rest)) :
    bytes.length = acc.length + n := by
  induction n generalizing bits acc with
  | zero =>
    simp only [Deflate.Spec.decodeStored.readNBytes] at h
    obtain ⟨rfl, _⟩ := Option.some.inj h; omega
  | succ k ih =>
    simp only [Deflate.Spec.decodeStored.readNBytes] at h
    cases hrd : Deflate.Spec.readBitsLSB 8 bits with
    | none => simp [hrd] at h
    | some p =>
      obtain ⟨v, bits'⟩ := p
      simp only [hrd, bind, Option.bind] at h
      have := ih h; simp at this; omega

/-- **Completeness for `readBytes`**: if the spec reads `n` bytes from
    an aligned position, the native `readBytes` succeeds with the same bytes. -/
theorem readBytes_complete (br : Zip.Native.BitReader) (n : Nat)
    (bytes : List UInt8) (rest : List Bool)
    (hwf : br.bitOff < 8)
    (hpos : br.bitOff = 0 ∨ br.pos < br.data.size)
    (halign_pos : br.alignToByte.pos ≤ br.alignToByte.data.size)
    (hspec : Deflate.Spec.decodeStored.readNBytes n
        (Deflate.Spec.alignToByte br.toBits) [] = some (bytes, rest)) :
    ∃ br', br.readBytes n = .ok (⟨⟨bytes⟩⟩, br') ∧
      br'.toBits = rest ∧
      br'.bitOff = 0 ∧
      (br'.bitOff = 0 ∨ br'.pos < br'.data.size) := by
  -- Rewrite spec hypothesis to use br.alignToByte.toBits
  have halign : br.alignToByte.toBits = Deflate.Spec.alignToByte br.toBits :=
    alignToByte_toBits br hwf hpos
  have hoff : br.alignToByte.bitOff = 0 := alignToByte_wf br
  rw [← halign] at hspec
  -- From readNBytes success, derive bounds
  have hbits_len := Deflate.Correctness.readNBytes_some_length hspec
  -- Derive pos + n ≤ data.size from halign_pos and bit count
  have hle : br.alignToByte.pos + n ≤ br.alignToByte.data.size := by
    rw [Deflate.Correctness.toBits_length, hoff, Nat.add_zero] at hbits_len; omega
  -- Use readNBytes_aligned to get the canonical form
  have hcanon := Deflate.Correctness.readNBytes_aligned br.alignToByte.data br.alignToByte.pos n hle []
  simp only [List.nil_append] at hcanon
  -- Both hspec and hcanon use readNBytes on the same drop expression
  simp only [Zip.Native.BitReader.toBits, hoff, Nat.add_zero] at hspec
  rw [hcanon] at hspec
  -- Extract equalities from injectivity
  simp only [Option.some.injEq, Prod.mk.injEq] at hspec
  obtain ⟨hbytes_eq, hrest_eq⟩ := hspec
  -- Unfold readBytes: aligns, bounds check passes
  have hbound_check : ¬(br.alignToByte.pos + n > br.alignToByte.data.size) := by omega
  -- Show bytes equality via ByteArray
  have hbytes_ba : br.alignToByte.data.extract br.alignToByte.pos (br.alignToByte.pos + n) = ⟨⟨bytes⟩⟩ := by
    apply ByteArray.ext
    exact Array.toList_inj.mp (by rw [ByteArray.data_extract, Array.toList_extract]; exact hbytes_eq)
  refine ⟨{ br.alignToByte with pos := br.alignToByte.pos + n }, ?_, ?_, alignToByte_wf br, Or.inl (alignToByte_wf br)⟩
  · -- readBytes succeeds
    simp only [Zip.Native.BitReader.readBytes, hbound_check, ↓reduceIte, hbytes_ba]
  · -- br'.toBits = rest
    rw [← hrest_eq]
    simp only [Zip.Native.BitReader.toBits, hoff, Nat.add_zero]

end Deflate.Correctness
