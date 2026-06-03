import Zip.Spec.BitstreamCorrect
import Zip.Spec.HuffmanCorrect

/-!
# Table-driven Huffman decode: equivalence to the tree walk

`HuffTree.decodeWithTable (buildTable tree)` (the fast-bits lookup decoder,
`Zip/Native/Inflate.lean`) is proven **equal** to the canonical bit-by-bit
`HuffTree.decode` tree walk — same symbol, same consumed `BitReader`, same
error behaviour. From that single-symbol lemma, `decodeHuffmanFast` (which the
block loop runs) is proven equal to `decodeHuffman` (the canonical spec), so
every existing inflate correctness proof transfers with one rewrite. There is
no `@[implemented_by]` trust gap: the fast path is on the verified route.
-/

namespace Zip.Native.HuffTree

open ZipCommon (BitReader)

/-- The codeword (`false = left`) of length `k` read from the low bits of `bits`,
    LSB first — exactly the path `tableEntry.go` walks (`bits % 2`, then
    `bits / 2`). -/
def cwOf : Nat → Nat → List Bool
  | _, 0 => []
  | bits, k + 1 => (bits % 2 == 1) :: cwOf (bits / 2) k

@[simp] theorem cwOf_length (bits k : Nat) : (cwOf bits k).length = k := by
  induction k generalizing bits with
  | zero => rfl
  | succ k ih => simp only [cwOf, List.length_cons, ih]

/-- A real leaf (`0 < len`) reached by `tableEntry.go` sits at depth `≥` the
    starting depth — given the start is within the `fastBits` window. -/
theorem tableEntry_go_depth_le (t : HuffTree) (bits depth : Nat)
    (sym : UInt16) (lenB : UInt8)
    (h : tableEntry.go t bits depth = (sym, lenB))
    (hd : depth ≤ fastBits) (hpos : 0 < lenB.toNat) :
    depth ≤ lenB.toNat := by
  induction t generalizing bits depth with
  | leaf s =>
    simp only [tableEntry.go, Prod.mk.injEq] at h
    obtain ⟨_, rfl⟩ := h
    have h1 : (depth.toUInt8).toNat = depth % 256 := by
      simp only [Nat.toUInt8, UInt8.ofNat, UInt8.toNat, BitVec.toNat_ofNat, Nat.reducePow]
    simp only [fastBits] at hd; omega
  | empty =>
    simp only [tableEntry.go, Prod.mk.injEq] at h; obtain ⟨_, rfl⟩ := h; simp at hpos
  | node z o ihz iho =>
    rw [tableEntry.go] at h
    split at h
    · simp only [Prod.mk.injEq] at h; obtain ⟨_, rfl⟩ := h; simp at hpos
    · rename_i hge
      have hd' : depth + 1 ≤ fastBits := by simp only [fastBits] at hge ⊢; omega
      split at h
      · have := ihz (bits / 2) (depth + 1) h hd'; omega
      · have := iho (bits / 2) (depth + 1) h hd'; omega

/-- **Codeword extraction.** A real leaf reached by `tableEntry.go t bits depth`
    sits at a `TreeHasLeaf` path equal to `cwOf bits (len - depth)`. -/
theorem hasLeaf_of_tableEntry_go (t : HuffTree) (bits depth : Nat)
    (sym : UInt16) (lenB : UInt8)
    (h : tableEntry.go t bits depth = (sym, lenB))
    (hlen : lenB.toNat ≤ fastBits) (hpos : 0 < lenB.toNat) (hdle : depth ≤ lenB.toNat) :
    Deflate.Correctness.TreeHasLeaf t (cwOf bits (lenB.toNat - depth)) sym := by
  induction t generalizing bits depth with
  | leaf s =>
    simp only [tableEntry.go, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    have h1 : (depth.toUInt8).toNat = depth % 256 := by
      simp only [Nat.toUInt8, UInt8.ofNat, UInt8.toNat, BitVec.toNat_ofNat, Nat.reducePow]
    rw [h1] at hdle ⊢
    have : depth % 256 - depth = 0 := by omega
    rw [this, cwOf]; exact .leaf
  | empty => simp only [tableEntry.go, Prod.mk.injEq] at h; obtain ⟨_, rfl⟩ := h; simp at hpos
  | node z o ihz iho =>
    rw [tableEntry.go] at h
    split at h
    · simp only [Prod.mk.injEq] at h; obtain ⟨_, rfl⟩ := h; simp at hpos
    · rename_i hge
      have hdf : depth < fastBits := by simp only [fastBits] at hge ⊢; omega
      have hdlt : depth < lenB.toNat := by
        split at h
        · have := tableEntry_go_depth_le z (bits / 2) (depth + 1) sym lenB h
            (by simp only [fastBits] at hdf ⊢; omega) hpos; omega
        · have := tableEntry_go_depth_le o (bits / 2) (depth + 1) sym lenB h
            (by simp only [fastBits] at hdf ⊢; omega) hpos; omega
      have hcw : lenB.toNat - depth = (lenB.toNat - (depth + 1)) + 1 := by omega
      rw [hcw, cwOf]
      split at h
      · rename_i hbit
        simp only [beq_iff_eq] at hbit
        have hb : (bits % 2 == 1) = false := by simp only [beq_eq_false_iff_ne]; omega
        rw [hb]
        exact .left (ihz (bits / 2) (depth + 1) h (by omega))
      · rename_i hbit
        simp only [beq_iff_eq] at hbit
        have hb : (bits % 2 == 1) = true := by simp only [beq_iff_eq]; omega
        rw [hb]
        exact .right (iho (bits / 2) (depth + 1) h (by omega))

/-- `cwOf`'s `j`-th bit is the `j`-th bit of `bits`. -/
theorem cwOf_getElem (bits k j : Nat) (hj : j < k) :
    (cwOf bits k)[j]'(by rw [cwOf_length]; exact hj) = bits.testBit j := by
  induction k generalizing bits j with
  | zero => omega
  | succ k ih =>
    cases j with
    | zero =>
      simp only [cwOf, List.getElem_cons_zero, Nat.testBit_zero]
      exact Bool.beq_eq_decide_eq (bits % 2) 1
    | succ j =>
      simp only [cwOf, List.getElem_cons_succ]
      rw [ih (bits / 2) j (by omega), Nat.testBit_add_one]

/-- `bytesToBits` indexes to the corresponding byte's bit. -/
theorem bytesToBits_getElem? (data : ByteArray) (g : Nat) (hg : g < data.size * 8) :
    (Deflate.Spec.bytesToBits data)[g]? = some (data[g / 8]!.toNat.testBit (g % 8)) := by
  have hq : g / 8 < data.size := by omega
  obtain ⟨rest, hrest⟩ :=
    Deflate.Correctness.bytesToBits_drop_testBit data (g / 8) (g % 8) hq (by omega)
  have hgg : g / 8 * 8 + g % 8 = g := by omega
  rw [hgg] at hrest
  rw [← List.head?_drop, hrest, List.head?_cons, getElem!_pos data (g / 8) hq]

/-- **peekFast bit correspondence.** Below `fastBits`, with enough bits left,
    the `j`-th peeked bit equals the `j`-th bit of the stream from the cursor. -/
theorem peekFast_testBit (br : BitReader) (j : Nat)
    (hwf : br.bitOff < 8) (hj : j < fastBits)
    (hg : br.pos * 8 + br.bitOff + j < br.data.size * 8) :
    (peekFast br).toNat.testBit j =
      br.data[(br.pos * 8 + br.bitOff + j) / 8]!.toNat.testBit
        ((br.pos * 8 + br.bitOff + j) % 8) := by
  have hpos : br.pos < br.data.size := by omega
  simp only [fastBits] at hj
  have hmask : (0x1FF : UInt32).toNat.testBit j = true := by
    rw [show (0x1FF : UInt32).toNat = 2 ^ 9 - 1 from by decide, Nat.testBit_two_pow_sub_one]
    simp only [decide_eq_true_eq]; omega
  have hshift : br.bitOff.toUInt32.toNat % 32 = br.bitOff := by
    simp only [Nat.toUInt32, UInt32.ofNat, UInt32.toNat, BitVec.toNat_ofNat, Nat.reducePow]
    omega
  unfold peekFast
  -- Reduce to a single-bit query on the 16-bit window `b0 ||| (b1 <<< 8)`.
  rw [UInt32.toNat_and, Nat.testBit_and, UInt32.toNat_shiftRight, Nat.testBit_shiftRight,
    hmask, Bool.and_true, hshift, UInt32.toNat_or, Nat.testBit_or,
    show (if br.pos < br.data.size then br.data[br.pos]!.toUInt32 else (0 : UInt32)).toNat
        = br.data[br.pos]!.toNat from by rw [if_pos hpos, UInt8.toNat_toUInt32]]
  -- The high byte `b1 <<< 8` (no UInt32 overflow: the value is < 2^16).
  have hb1eq : (if br.pos + 1 < br.data.size then br.data[br.pos + 1]!.toUInt32
        else (0 : UInt32)).toNat
      = (if br.pos + 1 < br.data.size then br.data[br.pos + 1]!.toNat else 0) := by
    split
    · rw [UInt8.toNat_toUInt32]
    · rfl
  have hb1lt : (if br.pos + 1 < br.data.size then br.data[br.pos + 1]!.toNat else 0) < 256 := by
    split
    · have := UInt8.toNat_lt br.data[br.pos + 1]!; omega
    · decide
  rw [UInt32.toNat_shiftLeft, show (8 : UInt32).toNat % 32 = 8 from by decide, hb1eq,
    Nat.mod_eq_of_lt (by rw [Nat.shiftLeft_eq, show (2 : Nat) ^ 8 = 256 from by decide,
      show (2 : Nat) ^ 32 = 4294967296 from by decide]; omega),
    Nat.testBit_shiftLeft]
  by_cases hlo : br.bitOff + j < 8
  · -- low byte: the shift-left term vanishes; cursor stays in byte `pos`
    rw [show (decide (br.bitOff + j ≥ 8)) = false from by
        simp only [decide_eq_false_iff_not]; omega, Bool.false_and, Bool.or_false,
      show (br.pos * 8 + br.bitOff + j) / 8 = br.pos from by omega,
      show (br.pos * 8 + br.bitOff + j) % 8 = br.bitOff + j from by omega]
  · -- high byte: byte `pos`'s bit is past its width (false); use byte `pos+1`
    rw [show br.data[br.pos]!.toNat.testBit (br.bitOff + j) = false from
        Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le (UInt8.toNat_lt br.data[br.pos]!)
          (Nat.pow_le_pow_right (by omega) (by omega))),
      show (decide (br.bitOff + j ≥ 8)) = true from by simp only [decide_eq_true_eq]; omega,
      Bool.true_and, Bool.false_or, if_pos (show br.pos + 1 < br.data.size from by omega),
      show (br.pos * 8 + br.bitOff + j) / 8 = br.pos + 1 from by omega,
      show (br.pos * 8 + br.bitOff + j) % 8 = br.bitOff + j - 8 from by omega]

/-- **Codeword = stream prefix.** With `bitOff < 8`, `len ≤ fastBits`, and at
    least `len` bits available, the codeword read from the peeked bits is the
    first `len` bits of the stream. -/
theorem cwOf_peekFast_eq_take (br : BitReader) (len : Nat)
    (hwf : br.bitOff < 8) (hlen : len ≤ fastBits) (havail : len ≤ bitsAvail br) :
    cwOf (peekFast br).toNat len = br.toBits.take len := by
  have hlb : len ≤ br.toBits.length := by
    rw [Deflate.Correctness.toBits_length]
    simp only [bitsAvail] at havail
    split at havail <;> omega
  apply List.ext_getElem?
  intro j
  rcases Nat.lt_or_ge j len with hj | hj
  · -- both indices yield `some (peeked bit j)`
    have hps : br.pos < br.data.size := by
      rcases Nat.lt_or_ge br.pos br.data.size with h | h
      · exact h
      · simp only [bitsAvail, if_pos h] at havail; omega
    have hgj : br.pos * 8 + br.bitOff + j < br.data.size * 8 := by
      simp only [bitsAvail, if_neg (Nat.not_le.mpr hps)] at havail; omega
    rw [List.getElem?_eq_getElem (by rw [cwOf_length]; exact hj), cwOf_getElem _ _ _ hj,
      List.getElem?_take_of_lt hj,
      show br.toBits = (Deflate.Spec.bytesToBits br.data).drop (br.pos * 8 + br.bitOff) from rfl,
      List.getElem?_drop, bytesToBits_getElem? _ _ hgj]
    congr 1
    exact peekFast_testBit br j hwf (by simp only [fastBits] at hlen ⊢; omega) hgj
  · rw [List.getElem?_eq_none (by rw [cwOf_length]; exact hj),
      List.getElem?_eq_none (by rw [List.length_take]; omega)]

/-- A real leaf reached by `tableEntry.go` from within the window sits at
    depth `≤ fastBits`. -/
theorem tableEntry_go_len_le (t : HuffTree) (bits depth : Nat)
    (sym : UInt16) (lenB : UInt8)
    (h : tableEntry.go t bits depth = (sym, lenB))
    (hd : depth ≤ fastBits) (hpos : 0 < lenB.toNat) :
    lenB.toNat ≤ fastBits := by
  induction t generalizing bits depth with
  | leaf s =>
    simp only [tableEntry.go, Prod.mk.injEq] at h
    obtain ⟨_, rfl⟩ := h
    have h1 : (depth.toUInt8).toNat = depth % 256 := by
      simp only [Nat.toUInt8, UInt8.ofNat, UInt8.toNat, BitVec.toNat_ofNat, Nat.reducePow]
    simp only [fastBits] at hd ⊢; omega
  | empty =>
    simp only [tableEntry.go, Prod.mk.injEq] at h; obtain ⟨_, rfl⟩ := h; simp at hpos
  | node z o ihz iho =>
    rw [tableEntry.go] at h
    split at h
    · simp only [Prod.mk.injEq] at h; obtain ⟨_, rfl⟩ := h; simp at hpos
    · rename_i hge
      have hd' : depth + 1 ≤ fastBits := by simp only [fastBits] at hge ⊢; omega
      split at h
      · exact ihz (bits / 2) (depth + 1) h hd'
      · exact iho (bits / 2) (depth + 1) h hd'

/-- `decode.go` only reads — it never changes the underlying `data`. -/
theorem decode_go_data (tree : HuffTree) (br : BitReader) (n : Nat)
    (sym : UInt16) (br' : BitReader)
    (h : Zip.Native.HuffTree.decode.go tree br n = .ok (sym, br')) : br'.data = br.data := by
  induction tree generalizing br n with
  | leaf s => simp only [HuffTree.decode.go, Except.ok.injEq, Prod.mk.injEq] at h; obtain ⟨_, rfl⟩ := h; rfl
  | empty => simp only [HuffTree.decode.go, reduceCtorEq] at h
  | node z o ihz iho =>
    simp only [HuffTree.decode.go] at h
    split at h
    · simp only [reduceCtorEq] at h
    · cases hrd : br.readBit with
      | error e => simp only [hrd, bind, Except.bind, reduceCtorEq] at h
      | ok p =>
        obtain ⟨bit, br₁⟩ := p
        have hdat : br₁.data = br.data := by
          simp only [ZipCommon.BitReader.readBit] at hrd
          split at hrd
          · exact nomatch hrd
          · split at hrd <;> simp only [Except.ok.injEq, Prod.mk.injEq] at hrd <;>
              (obtain ⟨_, rfl⟩ := hrd; rfl)
        simp only [hrd, bind, Except.bind] at h
        split at h
        · exact (ihz br₁ (n + 1) h).trans hdat
        · exact (iho br₁ (n + 1) h).trans hdat

/-- `decode.go` keeps the cursor within the data (it only reads). -/
theorem decode_go_pos_le (tree : HuffTree) (br : BitReader) (n : Nat)
    (sym : UInt16) (br' : BitReader)
    (h : Zip.Native.HuffTree.decode.go tree br n = .ok (sym, br'))
    (hle : br.pos ≤ br.data.size) : br'.pos ≤ br'.data.size := by
  induction tree generalizing br n with
  | leaf s =>
    simp only [HuffTree.decode.go, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨_, rfl⟩ := h; exact hle
  | empty => simp only [HuffTree.decode.go, reduceCtorEq] at h
  | node z o ihz iho =>
    simp only [HuffTree.decode.go] at h
    split at h
    · simp only [reduceCtorEq] at h
    · cases hrd : br.readBit with
      | error e => simp only [hrd, bind, Except.bind, reduceCtorEq] at h
      | ok p =>
        obtain ⟨bit, br₁⟩ := p
        have hle₁ : br₁.pos ≤ br₁.data.size := by
          simp only [ZipCommon.BitReader.readBit] at hrd
          split at hrd
          · exact nomatch hrd
          · rename_i hlt
            split at hrd <;> simp only [Except.ok.injEq, Prod.mk.injEq] at hrd <;>
              (obtain ⟨_, rfl⟩ := hrd; simp only []; omega)
        simp only [hrd, bind, Except.bind] at h
        split at h
        · exact ihz br₁ (n + 1) h hle₁
        · exact iho br₁ (n + 1) h hle₁

/-- Two readers over the same `data`, both with `bitOff < 8` and cursor within
    bounds, are equal when their remaining bit lists agree. -/
theorem br_eq_of_toBits (r1 r2 : BitReader)
    (hd : r1.data = r2.data) (htb : r1.toBits = r2.toBits)
    (hb1 : r1.pos * 8 + r1.bitOff ≤ r1.data.size * 8)
    (hb2 : r2.pos * 8 + r2.bitOff ≤ r2.data.size * 8)
    (hw1 : r1.bitOff < 8) (hw2 : r2.bitOff < 8) : r1 = r2 := by
  have hlen : r1.toBits.length = r2.toBits.length := by rw [htb]
  rw [Deflate.Correctness.toBits_length, Deflate.Correctness.toBits_length] at hlen
  have hsz : r1.data.size = r2.data.size := by rw [hd]
  obtain ⟨d1, p1, o1⟩ := r1; obtain ⟨d2, p2, o2⟩ := r2
  simp only at hd hsz hlen hb1 hb2 hw1 hw2 ⊢
  subst hd
  have : p1 = p2 ∧ o1 = o2 := by omega
  obtain ⟨rfl, rfl⟩ := this; rfl

/-- The reader `decodeWithTable` advances to (consume `k` bits from a
    well-formed cursor) is exactly the reader the tree walk reaches: same data,
    same remaining bits, same well-formed cursor. Isolated so the `BitReader`
    structure manipulation runs in a small goal context. -/
theorem advReader_eq (br br' : BitReader) (k : Nat)
    (hk : br.pos * 8 + br.bitOff + k ≤ br.data.size * 8)
    (hdata : br'.data = br.data)
    (hbits : br'.toBits = br.toBits.drop k)
    (hwf' : br'.bitOff < 8)
    (hpos' : br'.bitOff = 0 ∨ br'.pos < br'.data.size)
    (hposle' : br'.pos ≤ br'.data.size) :
    { br with pos := br.pos + (br.bitOff + k) / 8, bitOff := (br.bitOff + k) % 8 } = br' := by
  apply br_eq_of_toBits
  · rw [hdata]
  · rw [hbits]
    unfold ZipCommon.BitReader.toBits
    rw [List.drop_drop]
    dsimp only []
    congr 1
    omega
  · dsimp only []; omega
  · rw [hdata] at hposle' hpos' ⊢
    rcases hpos' with h0 | hlt <;> omega
  · dsimp only []; omega
  · exact hwf'

set_option maxRecDepth 4096 in
/-- **Symbol lemma.** The table-driven single-symbol decode built from `tree`
    agrees with the canonical tree walk, as a full `Except` result (same symbol
    *and* same resulting `BitReader`). Unconditional: `decodeWithTable` guards
    on `bitOff ≥ 8` (the only case where the fast path would diverge) by
    delegating to `decode`. -/
theorem decodeWithTable_eq (tree : HuffTree) (br : BitReader) :
    tree.decodeWithTable tree.buildTable br = tree.decode br := by
  have hidx : (peekFast br).toNat < 2 ^ fastBits := by
    unfold peekFast
    rw [UInt32.toNat_and]
    simp only [fastBits]
    exact Nat.and_lt_two_pow _ (by decide)
  have htab : (tree.buildTable)[(peekFast br).toNat]! = tableEntry tree (peekFast br).toNat := by
    unfold HuffTree.buildTable
    rw [getElem!_pos _ _ (by rw [Array.size_ofFn]; exact hidx), Array.getElem_ofFn]
  unfold HuffTree.decodeWithTable
  simp only []
  rw [htab]
  -- destructure the table entry into opaque `sym`, `lenB`
  generalize hentry : tableEntry tree (peekFast br).toNat = entry
  obtain ⟨sym, lenB⟩ := entry
  split
  · rfl
  · rename_i hwf8
    have hwf : br.bitOff < 8 := by omega
    split
    · rfl
    · rename_i hcond
      simp only [Bool.not_eq_true, Bool.or_eq_false_iff, beq_eq_false_iff_ne,
        decide_eq_false_iff_not, Nat.not_lt] at hcond
      obtain ⟨hlen0, havail⟩ := hcond
      have hpossize : br.pos < br.data.size := by
        rcases Nat.lt_or_ge br.pos br.data.size with h | h
        · exact h
        · exfalso; simp only [bitsAvail, if_pos h] at havail; omega
      have hgoeq : tableEntry.go tree (peekFast br).toNat 0 = (sym, lenB) := by
        rw [← hentry]; rfl
      have hlenfast : lenB.toNat ≤ fastBits :=
        tableEntry_go_len_le tree (peekFast br).toNat 0 sym lenB hgoeq (by simp [fastBits])
          (by omega)
      have hleaf : Deflate.Correctness.TreeHasLeaf tree
          (cwOf (peekFast br).toNat lenB.toNat) sym :=
        hasLeaf_of_tableEntry_go tree (peekFast br).toNat 0 sym lenB hgoeq hlenfast (by omega)
          (by omega)
      have hcw : cwOf (peekFast br).toNat lenB.toNat = br.toBits.take lenB.toNat :=
        cwOf_peekFast_eq_take br lenB.toNat hwf hlenfast havail
      have hsplit : br.toBits =
          cwOf (peekFast br).toNat lenB.toNat ++ br.toBits.drop lenB.toNat := by
        rw [hcw, List.take_append_drop]
      obtain ⟨br', hgo, hbits', hwf', hpos'⟩ :=
        Deflate.Correctness.decode_go_complete tree (cwOf (peekFast br).toNat lenB.toNat) sym
          (br.toBits.drop lenB.toNat) br 0 hleaf hwf (Or.inr hpossize) hsplit
          (by rw [cwOf_length]; simp only [fastBits] at hlenfast; omega)
      rw [HuffTree.decode, hgo]
      have hdata' : br'.data = br.data := decode_go_data tree br 0 sym br' hgo
      have hposle' : br'.pos ≤ br'.data.size := decode_go_pos_le tree br 0 sym br' hgo (by omega)
      have hk : br.pos * 8 + br.bitOff + lenB.toNat ≤ br.data.size * 8 := by
        have h1 : lenB.toNat + br.bitOff ≤ (br.data.size - br.pos) * 8 := by
          simp only [bitsAvail, if_neg (Nat.not_le.mpr hpossize)] at havail; omega
        have h2 : (br.data.size - br.pos) * 8 = br.data.size * 8 - br.pos * 8 := Nat.sub_mul _ _ _
        omega
      -- The explicit advanced reader equals `br'` (heavy reasoning isolated).
      exact congrArg Except.ok
        (Prod.ext rfl (advReader_eq br br' lenB.toNat hk hdata' hbits' hwf' hpos' hposle'))

end Zip.Native.HuffTree

namespace Zip.Native.Inflate

open ZipCommon (BitReader)

set_option maxRecDepth 4096 in
/-- **Loop lemma.** The table-driven block loop equals the canonical
    `decodeHuffman`: the two `.go` recursions have identical structure once each
    `decodeWithTable` is rewritten to `decode` via `decodeWithTable_eq`. By
    functional induction on `decodeHuffman.go`. -/
theorem decodeHuffmanFast_eq (br : BitReader) (output : ByteArray)
    (litTree distTree : HuffTree) (maxOut : Nat) :
    Inflate.decodeHuffmanFast br output litTree distTree maxOut
      = Inflate.decodeHuffman br output litTree distTree maxOut := by
  unfold Inflate.decodeHuffmanFast Inflate.decodeHuffman
  suffices H : ∀ (dataSize : Nat) (br : BitReader) (output : ByteArray),
      Inflate.decodeHuffmanFast.go litTree distTree maxOut
          litTree.buildTable distTree.buildTable dataSize br output
        = Inflate.decodeHuffman.go litTree distTree maxOut dataSize br output by
    exact H br.data.size br output
  intro dataSize br output
  induction br, output using
      Inflate.decodeHuffman.go.induct (maxOutputSize := maxOut) (dataSize := dataSize) with
  | _ br output ih_lit ih_ld =>
    unfold Inflate.decodeHuffmanFast.go Inflate.decodeHuffman.go
    rw [HuffTree.decodeWithTable_eq litTree br]
    cases hlit : litTree.decode br with
    | error e => rfl
    | ok p =>
      obtain ⟨sym, br₁⟩ := p
      simp only [bind, Except.bind]
      split
      · -- literal
        split
        · rfl
        · split
          · rfl
          · split
            · rfl
            · exact ih_lit sym br₁ ‹_› ‹_›
      · split
        · rfl
        · -- length/distance
          split
          · rfl
          · cases hext : br₁.readBits _ with
            | error e => rfl
            | ok pe =>
              obtain ⟨extraBits, br₂⟩ := pe
              dsimp only [Except.bind]
              rw [HuffTree.decodeWithTable_eq distTree br₂]
              cases hdist : distTree.decode br₂ with
              | error e => rfl
              | ok pd =>
                obtain ⟨distSym, br₃⟩ := pd
                dsimp only [Except.bind]
                split
                · rfl
                · cases hdext : br₃.readBits _ with
                  | error e => rfl
                  | ok pde =>
                    obtain ⟨dExtraBits, br₄⟩ := pde
                    dsimp only [Except.bind]
                    split
                    · rfl
                    · split
                      · rfl
                      · split
                        · rfl
                        · split
                          · rfl
                          · split
                            · rfl
                            · exact ih_ld sym ‹_› extraBits distSym ‹_› dExtraBits br₄ ‹_› ‹_› ‹_› ‹_›

end Zip.Native.Inflate
