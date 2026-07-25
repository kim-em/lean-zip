import Zip.Native.InflateFast
import Zip.Spec.InflateTreeFreeCorrect
import Zip.Spec.InflateWideRefillCorrect
import Zip.Spec.DecodeCorrect
import Zip.Spec.BitstreamCorrect

/-!
# Correctness of the write-once cursor decode (issue #2799)

This file proves the fastloop spikes of `Zip.Native.InflateFast` equal to the
verified reference loop `InflateBuf.goTreeFreeU`, so the write-once cursor
decoder inherits the whole `native ⊆ FFI` correctness story.

The heart is a **bisimulation** driven by one invariant: the reference threads a
growing `output` whose `.size` is the logical output length; the cursor loop
threads a fixed-size buffer plus a cursor `outPos`, and its logical content is
`buf.extract 0 outPos`. Both loops make identical control decisions because their
"logical output size" — `output.size` for the reference, `outPos` for the cursor
— stays equal, so every capacity / distance / max-size guard aligns. The output
side is bridged by two write lemmas:

* `set!` at the cursor, then extract, equals extract then `push` (a literal)
  — `set!_extract_eq_push` below;
* the inline short-match copy equals `copyWithinAt`, and `copyWithinAt` at the
  cursor, then extract, equals `copyLoop` on the logical prefix (a
  back-reference) — `copyWithinAtShort_eq` and
  `copyWithinAt_extract_eq_copyLoop` below.

Both need a **big-enough buffer** (`buf.size ≥ final reference size`), which is
carried through the induction and discharged at each step by the reference's
monotone output growth (`goTreeFree_size_mono`).

Status: **complete** (issue #2799) — this file is `sorry`-free. The chain, in
dependency order:
* the write bridges `set!_extract_eq_push` / `copyWithinAt_extract_eq_copyLoop`
  and reference monotonicity `goTreeFree_size_mono`, with all supporting
  `copyWithinAtGo` content lemmas and `getElem!` infrastructure;
* the **core bisimulation `goCur_eq`** — the write-once cursor decode agrees
  with `goTreeFreeU` — a 10-case functional induction over `goCur.induct`, plus
  `goCur_size` (the cursor preserves the buffer size);
* both **block bridges**: `decodeHuffmanCurTables_eq` (Huffman blocks, via
  `goCur_eq`) and `decodeStoredCur_eq` (stored blocks, via the `storedCopyLoop`
  content lemmas), each also concluding `cf.size = buf.size`;
* reference-loop output monotonicity `inflateLoopTreeFree_size_mono`;
* the **block-loop bisimulation `inflateLoopCur_eq`** — `inflateLoopCur`
  re-represents `inflateLoopTreeFree` block-for-block, applying the two bridges
  and threading `refOutput = buf.extract 0 outPos`;
* the target **`inflateFast_eq`**: whenever `Inflate.inflate` yields `out`, the
  write-once cursor decoder run at the exact size hint `out.size` yields the same
  bytes (`Inflate.inflate = inflateLoopTreeFree` by `inflateRaw_eq_loop`, then the
  loop bisimulation on the presized buffer, then the exact-size contract makes
  `cf = out`).

## The branch-free `uset` margin-split fastloop (the actual #2799 shape)

On top of the `set!` cursor, the same file proves the **branch-free `uset`
fastloop** `goCurU` — a per-symbol margin guard `outPos + 299 ≤ output.size`
gates a hot body that writes literals with proven-bounds `uset` (no per-literal
bounds check), copies non-overlapping matches of at most eight bytes with one
masked `ugetUInt64LE`/`usetUInt64LE` pair, drops the per-symbol max-size check,
and swaps `goCur`'s
`outPos + length > maxOut` guard for the cheaper `length > 258` — equal to
`goCur`. The centrepiece **`goCurU_eq`** is a 9-case functional induction over
`goCurU.induct` under the invariant `output.size ≤ maxOut`: the margin makes
`goCur`'s output-size checks unreachable (`ByteArray.uset_eq_set!`), and
`length_le_258` (a `decide` over the 29-entry length table, with `takeBits_lt`)
makes the two length guards agree; the `< 299`-byte tail is a literal delegation
to `goCur`. It lifts — every block decoder preserving the buffer size
(`decodeStoredCur_size`, `decodeHuffmanCurTables_size`, via `goCur_size`) — through
`decodeHuffmanCurTablesU_eq`, the block-loop bisimulation `inflateLoopCurU_eq`,
and `inflateRawFastU_eq`, to **`inflateFastU_eq`**: the `uset` fastloop composed
with `inflateFast_eq` decodes `Inflate.inflate` correctly.

## The reverse direction (soundness) and the production ratchet

`inflateFastU_eq` is forward-only (`inflate` accepts ⟹ fastloop accepts). The
**reverse** — fastloop accepts ⟹ `inflate` accepts — is a full reverse
bisimulation mirroring the forward chain: `goCur_treeFree` (reverse of
`goCur_eq`, using `goCur_outPos_mono` / `goCur_outPos_le_maxOut` to stay within
the exact-size buffer over `USize`), the reverse block bridges
`decodeStoredCur_treeFree` / `decodeHuffmanCurTables_treeFree`, and the reverse
loop `inflateLoopCur_treeFree` (with `inflateLoopCur_outPos_mono` bounding every
block cursor by the final one). Composed with `inflateLoopCur_size` and
`inflateRaw_eq_loop` this gives **`inflateFastU_sound`**, hence
**`inflateSized_agrees`**: the production dispatch `Inflate.inflateSized … =
Inflate.inflate` for every `USize`-representable input (under
`data.size, maxOut < USize.size` — the addressability regime, always true for
in-memory `ByteArray`s on a 64-bit target, that every native decode proof here
assumes). So the fastloop is a true ratchet, and wiring it into ZIP extraction
(`Zip.Archive`, size from the central-directory `uncompressedSize`, dispatch
guarded to stay in that regime) needs no checksum backstop for soundness. As
everywhere in this library, this is verified against the Lean reference bodies
of the `@[extern]` primitives (`presize`, `copyWithinAt`), which the C
implementations are trusted (and conformance-tested) to refine.

This file is imported by `Zip`, so the complete fastloop equivalence and
soundness chain is checked by the default library build and CI.
-/

namespace Zip.Native

open ByteArray (copyWithinAt copyWithinAtGo presize)

/-! ### `getElem!` helpers for list append / `ofFn` -/

theorem List.getElem!_append_left' {α} [Inhabited α] {l1 l2 : List α} {i : Nat}
    (h : i < l1.length) : (l1 ++ l2)[i]! = l1[i]! := by
  rw [getElem!_pos _ i (by simp only [List.length_append]; omega),
    List.getElem_append_left h, getElem!_pos l1 i h]

theorem List.getElem!_append_right' {α} [Inhabited α] {l1 l2 : List α} {i : Nat}
    (h : l1.length ≤ i) (h2 : i < l1.length + l2.length) :
    (l1 ++ l2)[i]! = l2[i - l1.length]! := by
  rw [getElem!_pos _ i (by simp only [List.length_append]; omega),
    List.getElem_append_right h, getElem!_pos l2 (i - l1.length) (by omega)]

theorem List.getElem!_ofFn' {α} [Inhabited α] {n : Nat} {f : Fin n → α} {i : Nat} (h : i < n) :
    (List.ofFn f)[i]! = f ⟨i, h⟩ := by
  rw [getElem!_pos _ i (by simp only [List.length_ofFn]; exact h), List.getElem_ofFn]

/-! ### Array-level write lemmas (the mathematical core) -/

/-- Setting index `i` in a big-enough array, then taking the `[0, i+1)` prefix,
    equals taking the `[0, i)` prefix and pushing the new value. Pure `Array`
    fact underlying the `ByteArray` cursor-literal write. -/
private theorem arr_setIfInBounds_extract_eq_push {α} (A : Array α) (i : Nat) (b : α)
    (h : i < A.size) :
    (A.setIfInBounds i b).extract 0 (i + 1) = (A.extract 0 i).push b := by
  apply Array.ext
  · simp only [Array.size_extract, Array.size_setIfInBounds, Array.size_push]; omega
  · intro j hj hj'
    simp only [Array.size_extract, Array.size_setIfInBounds, Nat.zero_add] at hj
    have hexi : (A.extract 0 i).size = i := by simp only [Array.size_extract]; omega
    grind

/-! ### `set!` cursor write vs `push` -/

/-- `ByteArray.set!` preserves size. -/
@[simp] theorem ByteArray.size_set! (a : ByteArray) (i : Nat) (v : UInt8) :
    (a.set! i v).size = a.size := by
  simp only [ByteArray.set!, ByteArray.size, Array.set!_eq_setIfInBounds,
    Array.size_setIfInBounds]

/-- `getElem!` of `set!`: the written slot reads `v` (in bounds), others unchanged. -/
theorem ByteArray.getElem!_set! (a : ByteArray) (i : Nat) (v : UInt8) (j : Nat) :
    (a.set! i v)[j]! = if j = i ∧ i < a.size then v else a[j]! := by
  by_cases hj : j < a.size
  · rw [getElem!_pos (a.set! i v) j (by rw [ByteArray.size_set!]; exact hj),
      getElem!_pos a j hj, ByteArray.getElem_eq_getElem_data, ByteArray.getElem_eq_getElem_data]
    simp only [ByteArray.set!, Array.set!_eq_setIfInBounds, Array.getElem_setIfInBounds,
      ByteArray.size_data]
    by_cases hji : i = j <;> grind
  · rw [getElem!_neg (a.set! i v) j (by rw [ByteArray.size_set!]; exact hj),
      getElem!_neg a j hj]
    simp only [show ¬ (j = i ∧ i < a.size) from fun hh => by omega, ↓reduceIte]

/-- Writing byte `b` at the cursor `outPos` into a big-enough buffer, then taking
    the `[0, outPos+1)` prefix, equals taking the `[0, outPos)` prefix and
    `push`ing `b` — i.e. the cursor `set!` realises a logical `push`. -/
theorem set!_extract_eq_push (a : ByteArray) (outPos : Nat) (b : UInt8)
    (h : outPos < a.size) :
    (a.set! outPos b).extract 0 (outPos + 1) = (a.extract 0 outPos).push b := by
  have hd : outPos < a.data.size := by simpa only [ByteArray.size_data] using h
  apply ByteArray.ext
  simp only [ByteArray.data_extract, ByteArray.set!, Array.set!_eq_setIfInBounds,
    ByteArray.data_push]
  exact arr_setIfInBounds_extract_eq_push a.data outPos b hd

/-! ### `copyWithinAt` cursor write vs `copyLoop`

`copyWithinAtGo` writes each slot `destOff + k` (`k < len`) as
`a[destOff - distance + k % distance]`, reading only the fixed window
`[destOff - distance, destOff)` (every read index is `< destOff`, below every
written position), and leaves positions outside `[destOff, destOff + len)`
untouched. This is the same periodic content that `copyLoop`'s
`copyLoop_eq_ofFn` characterisation appends. The two write lemmas below are the
back-reference analogue of `set!_extract_eq_push`. -/

/-- Size: `copyWithinAtGo` never grows the array (it is a chain of `set!`s). -/
theorem copyWithinAtGo_size (a : ByteArray) (destOff distance k len : Nat) :
    (copyWithinAtGo a destOff distance k len).size = a.size := by
  rw [copyWithinAtGo]
  split
  · rw [copyWithinAtGo_size (a.set! (destOff + k) _) destOff distance (k + 1) len,
      ByteArray.size_set!]
  · rfl
  termination_by len - k
  decreasing_by rename_i hk; omega

/-- `copyWithinAt` preserves size. -/
theorem copyWithinAt_size (a : ByteArray) (destOff distance len : Nat) :
    (a.copyWithinAt destOff distance len).size = a.size := by
  rw [ByteArray.copyWithinAt]; split
  · rfl
  · exact copyWithinAtGo_size a destOff distance 0 len

theorem ByteArray.getElem!_set (a : ByteArray) (i : Nat) (v : UInt8) (hi : i < a.size)
    (j : Nat) : (a.set i v hi)[j]! = if j = i then v else a[j]! := by
  by_cases hj : j < a.size
  · rw [getElem!_pos (a.set i v hi) j (by rw [ByteArray.size_set]; exact hj),
      getElem!_pos a j hj]
    by_cases hji : j = i
    · subst j
      simp only [ByteArray.getElem_eq_getElem_data, ByteArray.data_set,
        Array.getElem_set_self, ↓reduceIte]
    · simp only [ByteArray.getElem_eq_getElem_data, ByteArray.data_set,
        Array.getElem_set_ne hi hj (Ne.symm hji), hji, ↓reduceIte]
  · rw [getElem!_neg (a.set i v hi) j (by rw [ByteArray.size_set]; exact hj),
      getElem!_neg a j hj]
    simp only [if_neg (show j ≠ i by rintro rfl; exact hj hi)]

@[simp] theorem ByteArray.size_usetUInt64LE (a : ByteArray) (off : USize) (v : UInt64)
    (h : off.toNat + 8 ≤ a.size) : (a.usetUInt64LE off v h).size = a.size := by
  simp only [ByteArray.usetUInt64LE, ByteArray.size_set]

theorem ByteArray.getElem!_usetUInt64LE (a : ByteArray) (off : USize) (v : UInt64)
    (h : off.toNat + 8 ≤ a.size) (i : Nat) :
    (a.usetUInt64LE off v h)[i]! =
      if i = off.toNat + 7 then (v >>> 56).toUInt8
      else if i = off.toNat + 6 then (v >>> 48).toUInt8
      else if i = off.toNat + 5 then (v >>> 40).toUInt8
      else if i = off.toNat + 4 then (v >>> 32).toUInt8
      else if i = off.toNat + 3 then (v >>> 24).toUInt8
      else if i = off.toNat + 2 then (v >>> 16).toUInt8
      else if i = off.toNat + 1 then (v >>> 8).toUInt8
      else if i = off.toNat then v.toUInt8
      else a[i]! := by
  simp only [ByteArray.usetUInt64LE, ByteArray.getElem!_set]

theorem ByteArray.getElem!_usetUInt64LE_at (a : ByteArray) (off : USize) (v : UInt64)
    (h : off.toNat + 8 ≤ a.size) (k : Nat) (hk : k < 8) :
    (a.usetUInt64LE off v h)[off.toNat + k]! = (v >>> (k.toUInt64 <<< 3)).toUInt8 := by
  rw [ByteArray.getElem!_usetUInt64LE]
  have hcases : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨
      k = 6 ∨ k = 7 := by omega
  rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [Nat.toUInt64] <;> bv_decide

/-- Extracting each byte from an eight-byte little-endian recombination returns
    the corresponding input byte. -/
theorem UInt64.recomb8LE_bytes (a0 a1 a2 a3 a4 a5 a6 a7 : UInt8) :
    let w := a0.toUInt64 ||| (a1.toUInt64 <<< 8) ||| (a2.toUInt64 <<< 16) |||
      (a3.toUInt64 <<< 24) ||| (a4.toUInt64 <<< 32) ||| (a5.toUInt64 <<< 40) |||
      (a6.toUInt64 <<< 48) ||| (a7.toUInt64 <<< 56)
    w.toUInt8 = a0 ∧ (w >>> 8).toUInt8 = a1 ∧ (w >>> 16).toUInt8 = a2 ∧
      (w >>> 24).toUInt8 = a3 ∧ (w >>> 32).toUInt8 = a4 ∧
      (w >>> 40).toUInt8 = a5 ∧ (w >>> 48).toUInt8 = a6 ∧
      (w >>> 56).toUInt8 = a7 := by
  dsimp only
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> bv_decide

theorem ByteArray.ugetUInt64LE_byte (a : ByteArray) (off : USize)
    (h : off.toNat + 8 ≤ a.size) (k : Nat) (hk : k < 8) :
    (a.ugetUInt64LE off h >>> (k.toUInt64 <<< 3)).toUInt8 = a[off.toNat + k]! := by
  rw [getElem!_pos a (off.toNat + k) (by omega)]
  have hcases : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨
      k = 6 ∨ k = 7 := by omega
  have hb := UInt64.recomb8LE_bytes
    a[off.toNat] a[off.toNat + 1] a[off.toNat + 2] a[off.toNat + 3]
    a[off.toNat + 4] a[off.toNat + 5] a[off.toNat + 6] a[off.toNat + 7]
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩ := hb
  rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · simpa [ByteArray.ugetUInt64LE, Nat.toUInt64] using h0
  · simpa [ByteArray.ugetUInt64LE, Nat.toUInt64] using h1
  · simpa [ByteArray.ugetUInt64LE, Nat.toUInt64] using h2
  · simpa [ByteArray.ugetUInt64LE, Nat.toUInt64] using h3
  · simpa [ByteArray.ugetUInt64LE, Nat.toUInt64] using h4
  · simpa [ByteArray.ugetUInt64LE, Nat.toUInt64] using h5
  · simpa [ByteArray.ugetUInt64LE, Nat.toUInt64] using h6
  · simpa [ByteArray.ugetUInt64LE, Nat.toUInt64] using h7

theorem UInt64.blendLE_byte (src dst : UInt64) (len k : Nat)
    (hlenpos : 0 < len) (hlen : len ≤ 8) (hk : k < 8) :
    let mask := (0xffffffffffffffff : UInt64) >>> ((8 - len).toUInt64 <<< 3)
    (((src &&& mask) ||| (dst &&& ~~~mask)) >>> (k.toUInt64 <<< 3)).toUInt8 =
      if k < len then (src >>> (k.toUInt64 <<< 3)).toUInt8
      else (dst >>> (k.toUInt64 <<< 3)).toUInt8 := by
  dsimp only
  have hlcases : len = 1 ∨ len = 2 ∨ len = 3 ∨ len = 4 ∨ len = 5 ∨ len = 6 ∨
      len = 7 ∨ len = 8 := by omega
  have hkcases : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨
      k = 6 ∨ k = 7 := by omega
  rcases hlcases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hkcases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp [Nat.toUInt64] <;> bv_decide

/-- Content preservation below the cursor: `copyWithinAtGo` starting at counter
    `k` only writes positions `≥ destOff + k`, so positions `< destOff + k`
    (in particular the whole `[0, destOff)` window) are unchanged. -/
theorem copyWithinAtGo_getElem!_lt (a : ByteArray) (destOff distance k len i : Nat)
    (hi : i < destOff + k) :
    (copyWithinAtGo a destOff distance k len)[i]! = a[i]! := by
  rw [copyWithinAtGo]
  split
  · rename_i hk
    rw [copyWithinAtGo_getElem!_lt (a.set! (destOff + k) _) destOff distance (k + 1) len i
        (by omega), ByteArray.getElem!_set!]
    simp only [show ¬ (i = destOff + k ∧ destOff + k < a.size) from fun hh => by omega, ↓reduceIte]
  · rfl
  termination_by len - k
  decreasing_by rename_i hk; omega

/-- `ByteArray.get!` is `getElem!`. -/
theorem ByteArray.get!_eq_getElem! (a : ByteArray) (i : Nat) : a.get! i = a[i]! := by
  simp only [ByteArray.get!]
  by_cases hi : i < a.size
  · rw [getElem!_pos a i hi, getElem!_pos a.data i (by simpa only [ByteArray.size_data] using hi)]
    rfl
  · rw [getElem!_neg a i hi, getElem!_neg a.data i (by simpa only [ByteArray.size_data] using hi)]

/-- Written content of the cursor copy: for a position `destOff + j` in the
    write range (`k ≤ j < len`), the byte is the periodic window value
    `a[destOff - distance + (j % distance)]`. Every read stays in the fixed
    window `[destOff - distance, destOff)`, so the `set!`s never disturb it. -/
theorem copyWithinAtGo_getElem!_written (a : ByteArray) (destOff distance k len i : Nat)
    (hd : 0 < distance) (hdle : distance ≤ destOff) (hsz : destOff + len ≤ a.size)
    (hik : destOff + k ≤ i) (hil : i < destOff + len) :
    (copyWithinAtGo a destOff distance k len)[i]!
      = a[destOff - distance + ((i - destOff) % distance)]! := by
  rw [copyWithinAtGo, if_pos (show k < len by omega)]
  by_cases hik' : i = destOff + k
  · -- the position written at this step
    subst hik'
    rw [copyWithinAtGo_getElem!_lt _ destOff distance (k + 1) len (destOff + k) (by omega),
      ByteArray.getElem!_set!, if_pos ⟨rfl, by omega⟩, ByteArray.get!_eq_getElem!,
      show destOff + k - destOff = k from by omega]
  · -- a later position; recurse, and the write index is untouched by this set!
    have hidx : destOff - distance + (i - destOff) % distance < destOff := by
      have := Nat.mod_lt (i - destOff) hd; omega
    rw [copyWithinAtGo_getElem!_written (a.set! (destOff + k) _) destOff distance (k + 1) len i
        hd hdle (by rw [ByteArray.size_set!]; exact hsz) (by omega) hil,
      ByteArray.getElem!_set!, if_neg (by rintro ⟨h1, -⟩; omega)]
  termination_by len - k
  decreasing_by omega

/-- Positions at or above the end of the copy are unchanged. -/
theorem copyWithinAtGo_getElem!_ge (a : ByteArray) (destOff distance k len i : Nat)
    (hi : destOff + len ≤ i) :
    (copyWithinAtGo a destOff distance k len)[i]! = a[i]! := by
  rw [copyWithinAtGo]
  split
  · rename_i hk
    rw [copyWithinAtGo_getElem!_ge (a.set! (destOff + k) _) destOff distance (k + 1) len i hi,
      ByteArray.getElem!_set!]
    simp only [if_neg (show ¬(i = destOff + k ∧ destOff + k < a.size) from fun hh => by omega)]
  · rfl
  termination_by len - k
  decreasing_by rename_i hk; omega

/-- `copyLoop` (the reference back-reference append) grows the buffer by exactly
    `length`, derived from the `copyLoop_eq_ofFn` content characterisation. -/
theorem copyLoop_size (output : ByteArray) (length distance : Nat)
    (hd : 0 < distance) (hle : distance ≤ output.size) :
    (Inflate.copyLoop output (output.size - distance) distance 0 length hd (by omega)).size
      = output.size + length := by
  have h := congrArg List.length (Deflate.Correctness.copyLoop_eq_ofFn output length distance hd hle)
  simpa only [List.length_append, List.length_ofFn, Array.length_toList,
    ByteArray.size_data] using h

/-- Reference monotonicity: `goTreeFree` (the boxed reference loop) only grows
    its output, so any successful run ends no smaller than it started. This is
    what discharges the per-step "buffer has room" obligation in the
    bisimulation: at a write, the recursive reference's final size bounds the
    post-write size, which bounds the fixed cursor buffer's size. -/
theorem goTreeFree_size_mono (litTable distTable : HuffTree.DecodeTable)
    (litLD distLD : HuffTree.LongDecode) (maxBits : Nat) (data : ByteArray) (maxOut : Nat)
    (pos : Nat) (bitBuf : UInt64) (cnt : Nat) (output rf : ByteArray) (p : Nat) (b : UInt64) (c : Nat)
    (h : InflateBuf.goTreeFree litTable distTable litLD distLD maxBits data maxOut pos bitBuf cnt output
      = .ok (rf, p, b, c)) : output.size ≤ rf.size := by
  rw [InflateBuf.goTreeFree] at h
  split at h
  · -- refill: output unchanged
    exact goTreeFree_size_mono _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ h
  · split at h
    · -- literal fast path
      split at h
      · exact absurd h (by simp)                    -- output.size ≥ maxOut
      · have ih := goTreeFree_size_mono _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ h
        simp only [ByteArray.size_push] at ih; omega
    · -- long-code path
      split at h
      · exact absurd h (by simp)                    -- decodeSymCanon error
      · simp only at h
        split at h
        · -- long literal
          split at h
          · exact absurd h (by simp)                -- output.size ≥ maxOut
          · split at h
            · exact absurd h (by simp)               -- no-progress
            · have ih := goTreeFree_size_mono _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ h
              simp only [ByteArray.size_push] at ih; omega
        · split at h
          · -- EOB: rf = output
            simp only [Except.ok.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, _⟩ := h; exact Nat.le_refl _
          · -- back-reference (match)
            split at h
            · exact absurd h (by simp)               -- invalid length code
            · (try simp only [bind, Except.bind] at h)
              split at h
              · exact absurd h (by simp)             -- takeBits (length extra) error
              · split at h
                · exact absurd h (by simp)           -- distance decodeSymCanon error
                · split at h
                  · exact absurd h (by simp)         -- invalid distance code
                  · (try simp only [bind, Except.bind] at h)
                    split at h
                    · exact absurd h (by simp)       -- takeBits (dist extra) error
                    · split at h
                      · exact absurd h (by simp)     -- distance = 0
                      · split at h
                        · exact absurd h (by simp)   -- distance > output.size
                        · split at h
                          · exact absurd h (by simp) -- output.size + length > maxOut
                          · split at h
                            · exact absurd h (by simp) -- no-progress
                            · -- copyLoop then recurse
                              rename_i hz hds _ _
                              have ih := goTreeFree_size_mono _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ h
                              rw [copyLoop_size output _ _ (by omega) (by omega)] at ih
                              omega
  termination_by (data.size - pos) * 9 + cnt
  decreasing_by all_goals omega

/-! ### `copyWithinAt` cursor write vs `copyLoop` (back-reference)

The back-reference analogue of `set!_extract_eq_push`. Proof roadmap: both sides
have size `outPos + len` (`copyWithinAtGo_size` + `ByteArray.size_extract` on the
left; `copyLoop_size` on the right). Element-wise via `ByteArray.ext_getElem!`:
positions `< outPos` are preserved on both sides (`copyWithinAtGo_getElem!_lt`
for the cursor; the `output ++ …` prefix of `copyLoop_eq_ofFn` for the
reference); positions `outPos + k` (`k < len`) are the periodic window byte
`a[outPos - distance + k % distance]` on both sides — `copyWithinAtGo`'s content
theorem (the `_getElem!` companion to `_lt`, an induction reading only the fixed
window) versus the `List.ofFn` tail of `copyLoop_eq_ofFn`. -/
/-- `getElem!` extensionality for `ByteArray` (from the proof-carrying `ext_getElem`). -/
theorem ByteArray.ext_getElem! {a b : ByteArray} (h₀ : a.size = b.size)
    (h : ∀ i, i < a.size → a[i]! = b[i]!) : a = b := by
  apply ByteArray.ext_getElem h₀
  intro i hi hi'
  have := h i hi
  rwa [getElem!_pos a i hi, getElem!_pos b i hi'] at this

set_option maxHeartbeats 1000000 in
theorem ByteArray.copyWithinAtShort_eq (a : ByteArray) (destOff : USize)
    (distance len : Nat) (hdistance : 8 ≤ distance) (hlenpos : 0 < len) (hlen : len ≤ 8)
    (hwindow : distance ≤ destOff.toNat) (hroom : destOff.toNat + 8 ≤ a.size) :
    a.copyWithinAtShort destOff distance len hdistance hlenpos hlen hwindow hroom =
      a.copyWithinAt destOff.toNat distance len := by
  have hsrc : (destOff.toNat - distance).toUSize.toNat = destOff.toNat - distance :=
    InflateBuf.toUSize_toNat_of_lt
      (Nat.lt_of_le_of_lt (Nat.sub_le ..) destOff.toNat_lt_two_pow_numBits)
  rw [ByteArray.copyWithinAt, if_neg (by omega)]
  apply ByteArray.ext_getElem!
  · simp only [ByteArray.copyWithinAtShort, ByteArray.size_usetUInt64LE,
      copyWithinAtGo_size]
  · intro i hi
    simp only [ByteArray.copyWithinAtShort]
    by_cases hin : destOff.toNat ≤ i ∧ i < destOff.toNat + 8
    · let k := i - destOff.toNat
      have hk : k < 8 := by omega
      have hi' : i = destOff.toNat + k := by omega
      rw [hi', ByteArray.getElem!_usetUInt64LE_at _ _ _ _ k hk,
        UInt64.blendLE_byte _ _ len k hlenpos hlen hk]
      by_cases hkl : k < len
      · rw [if_pos hkl,
          copyWithinAtGo_getElem!_written a destOff.toNat distance 0 len (destOff.toNat + k)
            (by omega) hwindow (by omega) (by omega) (by omega)]
        rw [show (destOff.toNat + k - destOff.toNat) % distance = k by
          have : k < distance := by omega
          rw [show destOff.toNat + k - destOff.toNat = k by omega, Nat.mod_eq_of_lt this]]
        have hu := ByteArray.ugetUInt64LE_byte a (destOff.toNat - distance).toUSize
          (by rw [hsrc]; omega) k hk
        calc
          _ = a[(destOff.toNat - distance).toUSize.toNat + k]! := hu
          _ = a[destOff.toNat - distance + k]! := by rw [hsrc]
      · rw [if_neg hkl, copyWithinAtGo_getElem!_ge _ _ _ 0 _ _ (by omega)]
        exact ByteArray.ugetUInt64LE_byte a destOff hroom k hk
    · have hout : i < destOff.toNat ∨ destOff.toNat + 8 ≤ i := by omega
      rcases hout with hbelow | habove
      · rw [copyWithinAtGo_getElem!_lt _ _ _ 0 _ _ (by omega),
          ByteArray.getElem!_usetUInt64LE]
        have hne : ∀ k, k < 8 → i ≠ destOff.toNat + k := by omega
        simp only [if_neg (hne 7 (by omega)), if_neg (hne 6 (by omega)),
          if_neg (hne 5 (by omega)), if_neg (hne 4 (by omega)), if_neg (hne 3 (by omega)),
          if_neg (hne 2 (by omega)), if_neg (hne 1 (by omega)),
          if_neg (by simpa using hne 0 (by omega))]
      · rw [copyWithinAtGo_getElem!_ge _ _ _ 0 _ _ (by omega),
          ByteArray.getElem!_usetUInt64LE]
        have hne : ∀ k, k < 8 → i ≠ destOff.toNat + k := by omega
        simp only [if_neg (hne 7 (by omega)), if_neg (hne 6 (by omega)),
          if_neg (hne 5 (by omega)), if_neg (hne 4 (by omega)), if_neg (hne 3 (by omega)),
          if_neg (hne 2 (by omega)), if_neg (hne 1 (by omega)),
          if_neg (by simpa using hne 0 (by omega))]

/-- The short-match dispatch is extensionally just `copyWithinAt`; this packages
    the dependent branch proofs so callers can normalize the whole dispatch in
    one rewrite. -/
theorem ByteArray.copyWithinAtShort_if_eq (a : ByteArray) (destOff : USize)
    (distance len : Nat) (hlenpos : 0 < len) (hwindow : distance ≤ destOff.toNat)
    (hroom : destOff.toNat + 8 ≤ a.size) :
    (if hshort : 8 ≤ distance ∧ len ≤ 8 then
      a.copyWithinAtShort destOff distance len hshort.1 hlenpos hshort.2 hwindow hroom
    else a.copyWithinAt destOff.toNat distance len) =
      a.copyWithinAt destOff.toNat distance len := by
  split
  · apply ByteArray.copyWithinAtShort_eq
  · rfl

/-- `getElem!` of an extract prefix. -/
theorem ByteArray.getElem!_extract (x : ByteArray) (start stop i : Nat)
    (h : start + i < min stop x.size) : (x.extract start stop)[i]! = x[start + i]! := by
  have hsz : i < (x.extract start stop).size := by rw [ByteArray.size_extract]; omega
  rw [getElem!_pos _ i hsz, getElem!_pos x (start + i) (by omega), ByteArray.getElem_extract]

/-- `ByteArray` `getElem!` is the underlying array's list `getElem!`. -/
theorem ByteArray.getElem!_eq_data_toList (x : ByteArray) (i : Nat) :
    x[i]! = x.data.toList[i]! := by
  rw [← ByteArray.get!_eq_getElem!]
  simp only [ByteArray.get!]
  by_cases hi : i < x.data.size
  · rw [getElem!_pos x.data i hi, getElem!_pos x.data.toList i (by simpa using hi),
      Array.getElem_toList]
  · rw [getElem!_neg x.data i hi, getElem!_neg x.data.toList i (by simpa using hi)]

theorem copyWithinAt_extract_eq_copyLoop (a : ByteArray) (outPos distance len : Nat)
    (hd : 0 < distance) (hdle : distance ≤ outPos) (hlen : outPos + len ≤ a.size) :
    (a.copyWithinAt outPos distance len).extract 0 (outPos + len)
      = Inflate.copyLoop (a.extract 0 outPos) ((a.extract 0 outPos).size - distance) distance 0 len hd
          (by rw [ByteArray.size_extract]; omega) := by
  have hexP : (a.extract 0 outPos).size = outPos := by rw [ByteArray.size_extract]; omega
  rw [ByteArray.copyWithinAt,
    if_neg (show ¬(distance = 0 ∨ distance > outPos ∨ outPos + len > a.size) from by omega)]
  have hcl := Deflate.Correctness.copyLoop_eq_ofFn (a.extract 0 outPos) len distance hd
    (by rw [hexP]; exact hdle)
  apply ByteArray.ext_getElem!
  · rw [ByteArray.size_extract, copyWithinAtGo_size,
      copyLoop_size (a.extract 0 outPos) len distance hd (by rw [hexP]; exact hdle), hexP]
    omega
  · intro i hi
    rw [ByteArray.size_extract, copyWithinAtGo_size] at hi
    have hilt : i < outPos + len := by omega
    rw [ByteArray.getElem!_extract _ 0 (outPos + len) i (by rw [copyWithinAtGo_size]; omega),
      Nat.zero_add, ByteArray.getElem!_eq_data_toList (Inflate.copyLoop _ _ _ _ _ _ _), hcl]
    have hPlen : (a.extract 0 outPos).data.toList.length = outPos := by
      rw [Array.length_toList]; exact hexP
    rcases Nat.lt_or_ge i outPos with hio | hio
    · -- preserved prefix on both sides
      rw [copyWithinAtGo_getElem!_lt _ outPos distance 0 len i (by omega),
        List.getElem!_append_left' (by rw [hPlen]; exact hio),
        ← ByteArray.getElem!_eq_data_toList, ByteArray.getElem!_extract _ 0 outPos i (by omega),
        Nat.zero_add]
    · -- written window byte on both sides
      rw [copyWithinAtGo_getElem!_written a outPos distance 0 len i hd hdle hlen (by omega) hilt,
        List.getElem!_append_right' (by rw [hPlen]; exact hio)
          (by rw [hPlen, List.length_ofFn]; omega),
        hPlen, List.getElem!_ofFn' (show i - outPos < len by omega)]
      simp only [Fin.val_mk]
      rw [← ByteArray.getElem!_eq_data_toList,
        ByteArray.getElem!_extract _ 0 outPos _
          (by rw [Nat.lt_min]; have h1 := hexP; have := Nat.mod_lt (i - outPos) hd; omega),
        Nat.zero_add, hexP]

/-- `goTreeFreeU` output monotonicity, via `goTreeFreeU_eq` + `goTreeFree_size_mono`. -/
theorem goTreeFreeU_size_mono (litTable distTable : HuffTree.DecodeTable)
    (litLD distLD : HuffTree.LongDecode) (maxBits : Nat) (data : ByteArray) (maxOut : Nat)
    (hsz : data.size < USize.size) (hlp : litTable.packed.size = 2 ^ HuffTree.fastBits)
    (pos : USize) (bitBuf : UInt64) (cnt : USize) (output rf : ByteArray)
    (rp : USize) (rb : UInt64) (rc : USize) (hpos : pos.toNat ≤ data.size)
    (h : InflateBuf.goTreeFreeU litTable distTable litLD distLD maxBits data maxOut
      pos bitBuf cnt hsz hlp output = .ok (rf, rp, rb, rc)) :
    output.size ≤ rf.size := by
  have heq := InflateBuf.goTreeFreeU_eq litTable distTable data litLD distLD maxBits maxOut
    hsz hlp pos bitBuf cnt output hpos
  rw [h] at heq
  simp only [Except.map] at heq
  exact goTreeFree_size_mono litTable distTable litLD distLD maxBits data maxOut
    pos.toNat bitBuf cnt.toNat output rf rp.toNat rb rc.toNat heq.symm

/-! ### Bisimulation and lift

`goCur_eq` (the centrepiece, a 10-case induction over `goCur.induct` mirroring
`goTreeFreeU_eq`): under the invariant `buf.extract 0 outPos = refOutput` and the
big-enough-buffer hypothesis `refFinal.size ≤ buf.size` (discharged per step by
`goTreeFree_size_mono`), `goCur` returns the reference result re-represented
through the cursor — every guard aligns because `outPos = refOutput.size`, and
the two write steps are bridged by `set!_extract_eq_push` /
`copyWithinAt_extract_eq_copyLoop`. `goCurU_eq` then reduces the branch-free
`uset` fastloop to `goCur` (`uset = set` under the margin bound; the margin guard
only gates; the tail is literally `goCur`). Lifting through `decodeStoredCur` /
`decodeHuffmanCurTables` / `inflateLoopCur` yields the exact-size target below. -/

open InflateBuf (goCur goTreeFreeU refill refill_corr consume_corr BufCorr)

-- Force generation of the functional-induction principle for `goCur` so the
-- `induction … using goCur.induct` below can resolve it.
private def goCur_induct_force := @Zip.Native.InflateBuf.goCur.induct

set_option maxRecDepth 8192 in
/-- **The core bisimulation.** With the cursor logical content
    `buf.extract 0 outPos = refOutput`, a room bound `rf.size ≤ buf.size`, and the
    reference succeeding, `goCur` returns the same `(rp, rb, rc)` and a buffer
    whose `[0, rf.size)` prefix is `rf`, with cursor `rf.size`. Every guard aligns
    because `(buf.extract 0 outPos).size = outPos.toNat`; the write steps use the
    two write bridges; per-step room comes from `goTreeFreeU_size_mono`. Proved by
    `goCur.induct` (so the guards are named per case and no termination obligation
    remains), mirroring `goTreeFreeU_eq`. The goal side stays in `goCur`'s native
    `entryAtU` form (matching each IH); only `href` is normalised to `entryAt` via
    `entryAtU_window_eq`. -/
theorem goCur_eq (litTable distTable : HuffTree.DecodeTable) (litLD distLD : HuffTree.LongDecode)
    (maxBits : Nat) (data : ByteArray) (maxOut : Nat) (hsz : data.size < USize.size)
    (hlp : litTable.packed.size = 2 ^ HuffTree.fastBits) :
    ∀ (pos : USize) (bitBuf : UInt64) (cnt : USize) (buf : ByteArray) (outPos : USize),
    pos.toNat ≤ data.size → outPos.toNat ≤ buf.size → buf.size < USize.size →
    ∀ (rf : ByteArray) (rp : USize) (rb : UInt64) (rc : USize),
    goTreeFreeU litTable distTable litLD distLD maxBits data maxOut pos bitBuf cnt hsz hlp
        (buf.extract 0 outPos.toNat) = .ok (rf, rp, rb, rc) →
    rf.size ≤ buf.size →
    ∃ cf, goCur litTable distTable litLD distLD maxBits data maxOut pos bitBuf cnt hsz hlp buf outPos
      = .ok (cf, rf.size.toUSize, rp, rb, rc) ∧ cf.extract 0 rf.size = rf := by
  intro pos bitBuf cnt buf outPos
  induction pos, bitBuf, cnt, buf, outPos using goCur.induct
    (litTable := litTable) (litLD := litLD) (maxBits := maxBits) (data := data)
    (maxOut := maxOut) (hsz := hsz) (hlp := hlp) with
  | case1 pos bitBuf cnt buf outPos hrc ih =>
    intro hpos hout hbuf rf rp rb rc href hroom
    have hpn : pos.toNat < data.size := by
      have h := USize.lt_iff_toNat_lt.mp hrc.2; rwa [InflateBuf.toUSize_toNat_of_lt hsz] at h
    have hpa : (pos + 1).toNat = pos.toNat + 1 := by
      rw [USize.toNat_add, USize.toNat_one]; apply Nat.mod_eq_of_lt
      exact USize.size_eq_two_pow ▸ (show pos.toNat + 1 < USize.size by omega)
    rw [goTreeFreeU, dif_pos hrc] at href
    rw [goCur, dif_pos hrc]
    exact ih (by rw [hpa]; omega) hout hbuf rf rp rb rc href hroom
  | case2 pos bitBuf cnt buf outPos hrc ent hlit hmax =>
    intro hpos hout hbuf rf rp rb rc href hroom
    have hos : (buf.extract 0 outPos.toNat).size = outPos.toNat := by rw [ByteArray.size_extract]; omega
    have hue : ent = litTable.entryAt (bitBuf &&& 2047).toNat := litTable.entryAtU_window_eq bitBuf _
    have hlitA := hue ▸ hlit
    rw [goTreeFreeU, HuffTree.DecodeTable.entryAtU_window_eq, dif_neg hrc, dif_pos hlitA,
      if_pos (by rw [hos]; exact hmax)] at href
    exact absurd href (by simp)
  | case3 pos bitBuf cnt buf outPos hrc ent hlit hmax ih =>
    intro hpos hout hbuf rf rp rb rc href hroom
    have hos : (buf.extract 0 outPos.toNat).size = outPos.toNat := by rw [ByteArray.size_extract]; omega
    have houtsz : outPos.toNat < USize.size := Nat.lt_of_le_of_lt hout hbuf
    have hue : ent = litTable.entryAt (bitBuf &&& 2047).toNat := litTable.entryAtU_window_eq bitBuf _
    have hlitA := hue ▸ hlit
    rw [goTreeFreeU, HuffTree.DecodeTable.entryAtU_window_eq, dif_neg hrc, dif_pos hlitA,
      if_neg (by rw [hos]; exact hmax)] at href
    rw [goCur, HuffTree.DecodeTable.entryAtU_window_eq, dif_neg hrc, dif_pos hlitA, if_neg hmax]
    have hmono := goTreeFreeU_size_mono _ _ _ _ _ _ _ hsz hlp _ _ _ _ rf rp rb rc hpos href
    rw [ByteArray.size_push, hos] at hmono
    have hlt : outPos.toNat < buf.size := by omega
    have hop1 : (outPos + 1).toNat = outPos.toNat + 1 := by
      rw [USize.toNat_add, USize.toNat_one]; apply Nat.mod_eq_of_lt
      exact USize.size_eq_two_pow ▸ (show outPos.toNat + 1 < USize.size by omega)
    rw [← set!_extract_eq_push buf outPos.toNat _ hlt, ← hop1] at href
    exact (hue ▸ ih) hpos (by rw [ByteArray.size_set!, hop1]; omega) (by rw [ByteArray.size_set!]; exact hbuf)
      rf rp rb rc href (by rw [ByteArray.size_set!]; exact hroom)
  | case4 pos bitBuf cnt buf outPos hrc ent hlit e hde =>
    intro hpos hout hbuf rf rp rb rc href hroom
    have hue : ent = litTable.entryAt (bitBuf &&& 2047).toNat := litTable.entryAtU_window_eq bitBuf _
    have hlitA := hue ▸ hlit
    rw [goTreeFreeU, HuffTree.DecodeTable.entryAtU_window_eq, dif_neg hrc, dif_neg hlitA, hde] at href
    exact absurd href (by simp)
  | case5 pos bitBuf cnt buf outPos hrc ent hlit sym bb c' used hde hsym hmax =>
    intro hpos hout hbuf rf rp rb rc href hroom
    have hos : (buf.extract 0 outPos.toNat).size = outPos.toNat := by rw [ByteArray.size_extract]; omega
    have hue : ent = litTable.entryAt (bitBuf &&& 2047).toNat := litTable.entryAtU_window_eq bitBuf _
    have hlitA := hue ▸ hlit
    rw [goTreeFreeU, HuffTree.DecodeTable.entryAtU_window_eq, dif_neg hrc, dif_neg hlitA, hde] at href
    simp only [] at href
    rw [if_pos hsym, if_pos (by rw [hos]; exact hmax)] at href
    exact absurd href (by simp)
  | case6 pos bitBuf cnt buf outPos hrc ent hlit cnt0 sym bb c' used hde hsym hmax hnp =>
    intro hpos hout hbuf rf rp rb rc href hroom
    have hos : (buf.extract 0 outPos.toNat).size = outPos.toNat := by rw [ByteArray.size_extract]; omega
    have hue : ent = litTable.entryAt (bitBuf &&& 2047).toNat := litTable.entryAtU_window_eq bitBuf _
    have hlitA := hue ▸ hlit
    rw [goTreeFreeU, HuffTree.DecodeTable.entryAtU_window_eq, dif_neg hrc, dif_neg hlitA, hde] at href
    simp only [] at href
    rw [if_pos hsym, if_neg (by rw [hos]; exact hmax), dif_pos hnp] at href
    exact absurd href (by simp)
  | case7 pos bitBuf cnt buf outPos hrc ent hlit cnt0 sym bb c' used hde hsym hmax hnp ih =>
    intro hpos hout hbuf rf rp rb rc href hroom
    have hos : (buf.extract 0 outPos.toNat).size = outPos.toNat := by rw [ByteArray.size_extract]; omega
    have houtsz : outPos.toNat < USize.size := Nat.lt_of_le_of_lt hout hbuf
    have hue : ent = litTable.entryAt (bitBuf &&& 2047).toNat := litTable.entryAtU_window_eq bitBuf _
    have hlitA := hue ▸ hlit
    rw [goTreeFreeU, HuffTree.DecodeTable.entryAtU_window_eq, dif_neg hrc, dif_neg hlitA, hde] at href
    simp only [] at href
    rw [if_pos hsym, if_neg (by rw [hos]; exact hmax), dif_neg hnp] at href
    have hnp2 : ¬ cnt.toNat ≤ c' := hnp
    rw [goCur, dif_neg hrc, dif_neg hlit]
    simp only [hde, if_pos hsym, if_neg hmax, dif_neg hnp2]
    have hmono := goTreeFreeU_size_mono _ _ _ _ _ _ _ hsz hlp _ _ _ _ rf rp rb rc hpos href
    rw [ByteArray.size_push, hos] at hmono
    have hlt : outPos.toNat < buf.size := by omega
    have hop1 : (outPos + 1).toNat = outPos.toNat + 1 := by
      rw [USize.toNat_add, USize.toNat_one]; apply Nat.mod_eq_of_lt
      exact USize.size_eq_two_pow ▸ (show outPos.toNat + 1 < USize.size by omega)
    rw [← set!_extract_eq_push buf outPos.toNat _ hlt, ← hop1] at href
    exact ih hpos (by rw [ByteArray.size_set!, hop1]; omega) (by rw [ByteArray.size_set!]; exact hbuf)
      rf rp rb rc href (by rw [ByteArray.size_set!]; exact hroom)
  | case8 pos bitBuf cnt buf outPos hrc ent hlit sym bb c' used hde hsym heob =>
    intro hpos hout hbuf rf rp rb rc href hroom
    have hos : (buf.extract 0 outPos.toNat).size = outPos.toNat := by rw [ByteArray.size_extract]; omega
    have houtsz : outPos.toNat < USize.size := Nat.lt_of_le_of_lt hout hbuf
    have hue : ent = litTable.entryAt (bitBuf &&& 2047).toNat := litTable.entryAtU_window_eq bitBuf _
    have hlitA := hue ▸ hlit
    rw [goTreeFreeU, HuffTree.DecodeTable.entryAtU_window_eq, dif_neg hrc, dif_neg hlitA, hde] at href
    simp only [] at href
    rw [if_neg hsym, if_pos heob] at href
    simp only [Except.ok.injEq, Prod.mk.injEq] at href
    obtain ⟨rfl, rfl, rfl, rfl⟩ := href
    rw [goCur, dif_neg hrc, dif_neg hlit]
    simp only [hde, if_neg hsym, if_pos heob]
    have hop : outPos.toNat.toUSize = outPos :=
      USize.toNat_inj.mp (by rw [InflateBuf.toUSize_toNat_of_lt houtsz])
    refine ⟨buf, ?_, ?_⟩
    · rw [hos, hop]
    · rw [hos]
  | case9 pos bitBuf cnt buf outPos hrc ent hlit sym bb c' used hde hsym hneob idx hidx =>
    intro hpos hout hbuf rf rp rb rc href hroom
    have hue : ent = litTable.entryAt (bitBuf &&& 2047).toNat := litTable.entryAtU_window_eq bitBuf _
    have hlitA := hue ▸ hlit
    have hidx' : sym.toNat - 257 ≥ Inflate.lengthBase.size := hidx
    rw [goTreeFreeU, HuffTree.DecodeTable.entryAtU_window_eq, dif_neg hrc, dif_neg hlitA, hde] at href
    simp only [] at href
    rw [if_neg hsym, if_neg hneob, dif_pos hidx'] at href
    exact absurd href (by simp)
  | case10 pos bitBuf cnt buf outPos hrc ent hlit cnt0 sym bb c' used hde hsym hneob idx hh base ih =>
    intro hpos hout hbuf rf rp rb rc href hroom
    have hos : (buf.extract 0 outPos.toNat).size = outPos.toNat := by rw [ByteArray.size_extract]; omega
    have houtsz : outPos.toNat < USize.size := Nat.lt_of_le_of_lt hout hbuf
    have hue : ent = litTable.entryAt (bitBuf &&& 2047).toNat := litTable.entryAtU_window_eq bitBuf _
    have hlitA := hue ▸ hlit
    have hhc : ¬ sym.toNat - 257 ≥ Inflate.lengthBase.size := hh
    rw [goTreeFreeU, HuffTree.DecodeTable.entryAtU_window_eq, dif_neg hrc, dif_neg hlitA, hde] at href
    simp only [if_neg hsym, if_neg hneob, dif_neg hhc] at href
    rw [goCur, dif_neg hrc, dif_neg hlit]
    simp only [hde, if_neg hsym, if_neg hneob, dif_neg hhc]
    simp only [bind, Except.bind] at href ⊢
    cases htb : InflateBuf.takeBits bb c'
        (Inflate.lengthExtra[sym.toNat - 257]'(by
          simp only [Inflate.lengthExtra_size]
          simp only [Inflate.lengthBase_size, ge_iff_le, Nat.not_le] at hhc; omega)).toNat with
    | error e => rw [htb] at href; exact absurd href (by simp)
    | ok pe =>
      obtain ⟨eb, bb2, c2⟩ := pe
      rw [htb] at href
      simp only [] at href ⊢
      cases hde2 : HuffTree.decodeSymCanon distLD distTable maxBits bb2 c2 with
      | error e => rw [hde2] at href; exact absurd href (by simp)
      | ok pd =>
        obtain ⟨dsym, bb3, c3, dused⟩ := pd
        rw [hde2] at href
        simp only [] at href ⊢
        by_cases hdidx : dsym.toNat ≥ Inflate.distBase.size
        · rw [dif_pos hdidx] at href; exact absurd href (by simp)
        · rw [dif_neg hdidx] at href ⊢
          try simp only [bind, Except.bind] at href ⊢
          cases htb2 : InflateBuf.takeBits bb3 c3
              (Inflate.distExtra[dsym.toNat]'(by
                try simp only [Inflate.distBase_size, ge_iff_le, Nat.not_le] at hdidx
                try simp only [Inflate.distExtra_size]
                omega)).toNat with
          | error e => rw [htb2] at href; exact absurd href (by simp)
          | ok pd2 =>
            obtain ⟨deb, bb4, c4⟩ := pd2
            rw [htb2] at href
            simp only [] at href ⊢
            by_cases hz : Inflate.distBase[dsym.toNat].toNat + deb = 0
            · rw [dif_pos hz] at href; exact absurd href (by simp)
            · rw [dif_neg hz] at href ⊢
              by_cases hds : Inflate.distBase[dsym.toNat].toNat + deb > outPos.toNat
              · rw [dif_pos (by rw [hos]; exact hds)] at href; exact absurd href (by simp)
              · rw [dif_neg (by rw [hos]; exact hds)] at href
                rw [dif_neg hds]
                by_cases hmax :
                    outPos.toNat + (Inflate.lengthBase[sym.toNat - 257].toNat + eb) > maxOut
                · rw [if_pos (by rw [hos]; exact hmax)] at href; exact absurd href (by simp)
                · rw [if_neg (by rw [hos]; exact hmax)] at href
                  rw [if_neg hmax]
                  by_cases hnp : cnt.toNat ≤ c4
                  · rw [dif_pos hnp] at href; exact absurd href (by simp)
                  · rw [dif_neg hnp] at href
                    rw [dif_neg hnp]
                    have hd0 : 0 < Inflate.distBase[dsym.toNat].toNat + deb := by omega
                    have hdle : Inflate.distBase[dsym.toNat].toNat + deb ≤ outPos.toNat := by omega
                    have hmono := goTreeFreeU_size_mono _ _ _ _ _ _ _ hsz hlp _ _ _ _
                      rf rp rb rc hpos href
                    rw [copyLoop_size (buf.extract 0 outPos.toNat) _ _ hd0 (by rw [hos]; exact hdle),
                      hos] at hmono
                    have hlen : outPos.toNat + (Inflate.lengthBase[sym.toNat - 257].toNat + eb)
                        ≤ buf.size := by omega
                    have hlenlt : Inflate.lengthBase[sym.toNat - 257].toNat + eb < USize.size := by
                      omega
                    have hadv : (outPos + (Inflate.lengthBase[sym.toNat - 257].toNat + eb).toUSize).toNat
                        = outPos.toNat + (Inflate.lengthBase[sym.toNat - 257].toNat + eb) := by
                      rw [USize.toNat_add, InflateBuf.toUSize_toNat_of_lt hlenlt]
                      apply Nat.mod_eq_of_lt
                      exact USize.size_eq_two_pow ▸ (show outPos.toNat
                        + (Inflate.lengthBase[sym.toNat - 257].toNat + eb) < USize.size by omega)
                    rw [← copyWithinAt_extract_eq_copyLoop buf outPos.toNat _ _ hd0 hdle hlen,
                      ← hadv] at href
                    exact ih eb dsym hdidx deb bb4 c4 hnp hpos
                      (by rw [copyWithinAt_size, hadv]; omega)
                      (by rw [copyWithinAt_size]; exact hbuf) rf rp rb rc href
                      (by rw [copyWithinAt_size]; exact hroom)

set_option maxRecDepth 8192 in
/-- **`goCur` preserves the buffer size** (it only ever `set!`s / `copyWithinAt`s
    into the fixed buffer, or returns it at end-of-block). Needed so the loop lift
    can thread the room bound and the exact-size contract. -/
theorem goCur_size (litTable distTable : HuffTree.DecodeTable) (litLD distLD : HuffTree.LongDecode)
    (maxBits : Nat) (data : ByteArray) (maxOut : Nat) (hsz : data.size < USize.size)
    (hlp : litTable.packed.size = 2 ^ HuffTree.fastBits) :
    ∀ (pos : USize) (bitBuf : UInt64) (cnt : USize) (buf : ByteArray) (outPos : USize)
      (cf : ByteArray) (c2 rp : USize) (rb : UInt64) (rc : USize),
    goCur litTable distTable litLD distLD maxBits data maxOut pos bitBuf cnt hsz hlp buf outPos
      = .ok (cf, c2, rp, rb, rc) → cf.size = buf.size := by
  intro pos bitBuf cnt buf outPos
  induction pos, bitBuf, cnt, buf, outPos using goCur.induct
    (litTable := litTable) (litLD := litLD) (maxBits := maxBits) (data := data)
    (maxOut := maxOut) (hsz := hsz) (hlp := hlp) with
  | case1 pos bitBuf cnt buf outPos hrc ih =>
    intro cf c2 rp rb rc h; rw [goCur, dif_pos hrc] at h; exact ih cf c2 rp rb rc h
  | case2 pos bitBuf cnt buf outPos hrc ent hlit hmax =>
    intro cf c2 rp rb rc h; rw [goCur, dif_neg hrc, dif_pos hlit, if_pos hmax] at h
    exact absurd h (by simp)
  | case3 pos bitBuf cnt buf outPos hrc ent hlit hmax ih =>
    intro cf c2 rp rb rc h; rw [goCur, dif_neg hrc, dif_pos hlit, if_neg hmax] at h
    have := ih cf c2 rp rb rc h; rwa [ByteArray.size_set!] at this
  | case4 pos bitBuf cnt buf outPos hrc ent hlit e hde =>
    intro cf c2 rp rb rc h; rw [goCur, dif_neg hrc, dif_neg hlit, hde] at h
    exact absurd h (by simp)
  | case5 pos bitBuf cnt buf outPos hrc ent hlit sym bb c' used hde hsym hmax =>
    intro cf c2 rp rb rc h; rw [goCur, dif_neg hrc, dif_neg hlit, hde] at h
    simp only [] at h; rw [if_pos hsym, if_pos hmax] at h; exact absurd h (by simp)
  | case6 pos bitBuf cnt buf outPos hrc ent hlit cnt0 sym bb c' used hde hsym hmax hnp =>
    intro cf c2 rp rb rc h; rw [goCur, dif_neg hrc, dif_neg hlit, hde] at h
    simp only [] at h; rw [if_pos hsym, if_neg hmax, dif_pos hnp] at h; exact absurd h (by simp)
  | case7 pos bitBuf cnt buf outPos hrc ent hlit cnt0 sym bb c' used hde hsym hmax hnp ih =>
    intro cf c2 rp rb rc h; rw [goCur, dif_neg hrc, dif_neg hlit, hde] at h
    simp only [] at h; rw [if_pos hsym, if_neg hmax, dif_neg hnp] at h
    have := ih cf c2 rp rb rc h; rwa [ByteArray.size_set!] at this
  | case8 pos bitBuf cnt buf outPos hrc ent hlit sym bb c' used hde hsym heob =>
    intro cf c2 rp rb rc h; rw [goCur, dif_neg hrc, dif_neg hlit, hde] at h
    simp only [] at h; rw [if_neg hsym, if_pos heob] at h
    simp only [Except.ok.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, _⟩ := h; rfl
  | case9 pos bitBuf cnt buf outPos hrc ent hlit sym bb c' used hde hsym hneob idx hidx =>
    intro cf c2 rp rb rc h; rw [goCur, dif_neg hrc, dif_neg hlit, hde] at h
    simp only [] at h
    rw [if_neg hsym, if_neg hneob, dif_pos (show sym.toNat - 257 ≥ Inflate.lengthBase.size from hidx)] at h
    exact absurd h (by simp)
  | case10 pos bitBuf cnt buf outPos hrc ent hlit cnt0 sym bb c' used hde hsym hneob idx hh base ih =>
    intro cf c2 rp rb rc h
    have hhc : ¬ sym.toNat - 257 ≥ Inflate.lengthBase.size := hh
    rw [goCur, dif_neg hrc, dif_neg hlit, hde] at h
    simp only [if_neg hsym, if_neg hneob, dif_neg hhc, bind, Except.bind] at h
    cases htb : InflateBuf.takeBits bb c'
        (Inflate.lengthExtra[sym.toNat - 257]'(by
          simp only [Inflate.lengthExtra_size]
          simp only [Inflate.lengthBase_size, ge_iff_le, Nat.not_le] at hhc; omega)).toNat with
    | error e => rw [htb] at h; exact absurd h (by simp)
    | ok pe =>
      obtain ⟨eb, bb2, c2'⟩ := pe; rw [htb] at h; simp only [] at h
      cases hde2 : HuffTree.decodeSymCanon distLD distTable maxBits bb2 c2' with
      | error e => rw [hde2] at h; exact absurd h (by simp)
      | ok pd =>
        obtain ⟨dsym, bb3, c3, dused⟩ := pd; rw [hde2] at h; simp only [] at h
        by_cases hdidx : dsym.toNat ≥ Inflate.distBase.size
        · rw [dif_pos hdidx] at h; exact absurd h (by simp)
        · rw [dif_neg hdidx] at h; try simp only [bind, Except.bind] at h
          cases htb2 : InflateBuf.takeBits bb3 c3
              (Inflate.distExtra[dsym.toNat]'(by
                try simp only [Inflate.distBase_size, ge_iff_le, Nat.not_le] at hdidx
                try simp only [Inflate.distExtra_size]
                omega)).toNat with
          | error e => rw [htb2] at h; exact absurd h (by simp)
          | ok pd2 =>
            obtain ⟨deb, bb4, c4⟩ := pd2; rw [htb2] at h; simp only [] at h
            by_cases hz : Inflate.distBase[dsym.toNat].toNat + deb = 0
            · rw [dif_pos hz] at h; exact absurd h (by simp)
            · rw [dif_neg hz] at h
              by_cases hds : Inflate.distBase[dsym.toNat].toNat + deb > outPos.toNat
              · rw [dif_pos hds] at h; exact absurd h (by simp)
              · rw [dif_neg hds] at h
                by_cases hmax : outPos.toNat + (Inflate.lengthBase[sym.toNat - 257].toNat + eb) > maxOut
                · rw [if_pos hmax] at h; exact absurd h (by simp)
                · rw [if_neg hmax] at h
                  by_cases hnp : cnt.toNat ≤ c4
                  · rw [dif_pos hnp] at h; exact absurd h (by simp)
                  · rw [dif_neg hnp] at h
                    have := ih eb dsym hdidx deb bb4 c4 hnp cf c2 rp rb rc h
                    rwa [copyWithinAt_size] at this

set_option maxRecDepth 8192 in
/-- **`goCur` never moves the cursor backward** (`outPos ≤ final outPos`). Needed by
    the reverse bisimulation to keep every intermediate cursor within the exact-size
    buffer. `maxOut < USize.size` bounds the per-step advance so the `USize` adds
    don't wrap. -/
theorem goCur_outPos_mono (litTable distTable : HuffTree.DecodeTable) (litLD distLD : HuffTree.LongDecode)
    (maxBits : Nat) (data : ByteArray) (maxOut : Nat) (hsz : data.size < USize.size)
    (hlp : litTable.packed.size = 2 ^ HuffTree.fastBits) (hmo : maxOut < USize.size) :
    ∀ (pos : USize) (bitBuf : UInt64) (cnt : USize) (buf : ByteArray) (outPos : USize)
      (cf : ByteArray) (c2 rp : USize) (rb : UInt64) (rc : USize),
    goCur litTable distTable litLD distLD maxBits data maxOut pos bitBuf cnt hsz hlp buf outPos
      = .ok (cf, c2, rp, rb, rc) → outPos.toNat ≤ c2.toNat := by
  intro pos bitBuf cnt buf outPos
  induction pos, bitBuf, cnt, buf, outPos using goCur.induct
    (litTable := litTable) (litLD := litLD) (maxBits := maxBits) (data := data)
    (maxOut := maxOut) (hsz := hsz) (hlp := hlp) with
  | case1 pos bitBuf cnt buf outPos hrc ih =>
    intro cf c2 rp rb rc h; rw [goCur, dif_pos hrc] at h; exact ih cf c2 rp rb rc h
  | case2 pos bitBuf cnt buf outPos hrc ent hlit hmax =>
    intro cf c2 rp rb rc h; rw [goCur, dif_neg hrc, dif_pos hlit, if_pos hmax] at h
    exact absurd h (by simp)
  | case3 pos bitBuf cnt buf outPos hrc ent hlit hmax ih =>
    intro cf c2 rp rb rc h; rw [goCur, dif_neg hrc, dif_pos hlit, if_neg hmax] at h
    have hlt : outPos.toNat < maxOut := Nat.not_le.mp hmax
    have hop1 : (outPos + 1).toNat = outPos.toNat + 1 := by
      rw [USize.toNat_add, USize.toNat_one]; apply Nat.mod_eq_of_lt
      exact USize.size_eq_two_pow ▸ (show outPos.toNat + 1 < USize.size by omega)
    have := ih cf c2 rp rb rc h; omega
  | case4 pos bitBuf cnt buf outPos hrc ent hlit e hde =>
    intro cf c2 rp rb rc h; rw [goCur, dif_neg hrc, dif_neg hlit, hde] at h
    exact absurd h (by simp)
  | case5 pos bitBuf cnt buf outPos hrc ent hlit sym bb c' used hde hsym hmax =>
    intro cf c2 rp rb rc h; rw [goCur, dif_neg hrc, dif_neg hlit, hde] at h
    simp only [] at h; rw [if_pos hsym, if_pos hmax] at h; exact absurd h (by simp)
  | case6 pos bitBuf cnt buf outPos hrc ent hlit cnt0 sym bb c' used hde hsym hmax hnp =>
    intro cf c2 rp rb rc h; rw [goCur, dif_neg hrc, dif_neg hlit, hde] at h
    simp only [] at h; rw [if_pos hsym, if_neg hmax, dif_pos hnp] at h; exact absurd h (by simp)
  | case7 pos bitBuf cnt buf outPos hrc ent hlit cnt0 sym bb c' used hde hsym hmax hnp ih =>
    intro cf c2 rp rb rc h; rw [goCur, dif_neg hrc, dif_neg hlit, hde] at h
    simp only [] at h; rw [if_pos hsym, if_neg hmax, dif_neg hnp] at h
    have hlt : outPos.toNat < maxOut := Nat.not_le.mp hmax
    have hop1 : (outPos + 1).toNat = outPos.toNat + 1 := by
      rw [USize.toNat_add, USize.toNat_one]; apply Nat.mod_eq_of_lt
      exact USize.size_eq_two_pow ▸ (show outPos.toNat + 1 < USize.size by omega)
    have := ih cf c2 rp rb rc h; omega
  | case8 pos bitBuf cnt buf outPos hrc ent hlit sym bb c' used hde hsym heob =>
    intro cf c2 rp rb rc h; rw [goCur, dif_neg hrc, dif_neg hlit, hde] at h
    simp only [] at h; rw [if_neg hsym, if_pos heob] at h
    simp only [Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨_, hc2, _⟩ := h; subst hc2; exact Nat.le_refl _
  | case9 pos bitBuf cnt buf outPos hrc ent hlit sym bb c' used hde hsym hneob idx hidx =>
    intro cf c2 rp rb rc h; rw [goCur, dif_neg hrc, dif_neg hlit, hde] at h
    simp only [] at h
    rw [if_neg hsym, if_neg hneob, dif_pos (show sym.toNat - 257 ≥ Inflate.lengthBase.size from hidx)] at h
    exact absurd h (by simp)
  | case10 pos bitBuf cnt buf outPos hrc ent hlit cnt0 sym bb c' used hde hsym hneob idx hh base ih =>
    intro cf c2 rp rb rc h
    have hhc : ¬ sym.toNat - 257 ≥ Inflate.lengthBase.size := hh
    rw [goCur, dif_neg hrc, dif_neg hlit, hde] at h
    simp only [if_neg hsym, if_neg hneob, dif_neg hhc, bind, Except.bind] at h
    cases htb : InflateBuf.takeBits bb c'
        (Inflate.lengthExtra[sym.toNat - 257]'(by
          simp only [Inflate.lengthExtra_size]
          simp only [Inflate.lengthBase_size, ge_iff_le, Nat.not_le] at hhc; omega)).toNat with
    | error e => rw [htb] at h; exact absurd h (by simp)
    | ok pe =>
      obtain ⟨eb, bb2, c2'⟩ := pe; rw [htb] at h; simp only [] at h
      cases hde2 : HuffTree.decodeSymCanon distLD distTable maxBits bb2 c2' with
      | error e => rw [hde2] at h; exact absurd h (by simp)
      | ok pd =>
        obtain ⟨dsym, bb3, c3, dused⟩ := pd; rw [hde2] at h; simp only [] at h
        by_cases hdidx : dsym.toNat ≥ Inflate.distBase.size
        · rw [dif_pos hdidx] at h; exact absurd h (by simp)
        · rw [dif_neg hdidx] at h; try simp only [bind, Except.bind] at h
          cases htb2 : InflateBuf.takeBits bb3 c3
              (Inflate.distExtra[dsym.toNat]'(by
                try simp only [Inflate.distBase_size, ge_iff_le, Nat.not_le] at hdidx
                try simp only [Inflate.distExtra_size]
                omega)).toNat with
          | error e => rw [htb2] at h; exact absurd h (by simp)
          | ok pd2 =>
            obtain ⟨deb, bb4, c4⟩ := pd2; rw [htb2] at h; simp only [] at h
            by_cases hz : Inflate.distBase[dsym.toNat].toNat + deb = 0
            · rw [dif_pos hz] at h; exact absurd h (by simp)
            · rw [dif_neg hz] at h
              by_cases hds : Inflate.distBase[dsym.toNat].toNat + deb > outPos.toNat
              · rw [dif_pos hds] at h; exact absurd h (by simp)
              · rw [dif_neg hds] at h
                by_cases hmax : outPos.toNat + (Inflate.lengthBase[sym.toNat - 257].toNat + eb) > maxOut
                · rw [if_pos hmax] at h; exact absurd h (by simp)
                · rw [if_neg hmax] at h
                  by_cases hnp : cnt.toNat ≤ c4
                  · rw [dif_pos hnp] at h; exact absurd h (by simp)
                  · rw [dif_neg hnp] at h
                    have hle : outPos.toNat + (Inflate.lengthBase[sym.toNat - 257].toNat + eb) ≤ maxOut :=
                      Nat.not_lt.mp hmax
                    have hlenlt : Inflate.lengthBase[sym.toNat - 257].toNat + eb < USize.size :=
                      Nat.lt_of_le_of_lt (Nat.le_trans (Nat.le_add_left _ _) hle) hmo
                    have hadv : (outPos + (Inflate.lengthBase[sym.toNat - 257].toNat + eb).toUSize).toNat
                        = outPos.toNat + (Inflate.lengthBase[sym.toNat - 257].toNat + eb) := by
                      rw [USize.toNat_add, InflateBuf.toUSize_toNat_of_lt hlenlt]
                      apply Nat.mod_eq_of_lt
                      exact USize.size_eq_two_pow ▸ Nat.lt_of_le_of_lt hle hmo
                    have hmono := ih eb dsym hdidx deb bb4 c4 hnp cf c2 rp rb rc h
                    exact Nat.le_trans (hadv.symm ▸ Nat.le_add_right outPos.toNat _) hmono

set_option maxRecDepth 8192 in
/-- **`goCur`'s output cursor stays `≤ maxOut`** (the per-symbol max-size checks
    keep every write in budget). Gives `finalCursor < USize.size` for the loop-level
    monotonicity, so the reverse loop's block-mono recursion is well-bounded. -/
theorem goCur_outPos_le_maxOut (litTable distTable : HuffTree.DecodeTable) (litLD distLD : HuffTree.LongDecode)
    (maxBits : Nat) (data : ByteArray) (maxOut : Nat) (hsz : data.size < USize.size)
    (hlp : litTable.packed.size = 2 ^ HuffTree.fastBits) (hmo : maxOut < USize.size) :
    ∀ (pos : USize) (bitBuf : UInt64) (cnt : USize) (buf : ByteArray) (outPos : USize),
    outPos.toNat ≤ maxOut →
    ∀ (cf : ByteArray) (c2 rp : USize) (rb : UInt64) (rc : USize),
    goCur litTable distTable litLD distLD maxBits data maxOut pos bitBuf cnt hsz hlp buf outPos
      = .ok (cf, c2, rp, rb, rc) → c2.toNat ≤ maxOut := by
  intro pos bitBuf cnt buf outPos
  induction pos, bitBuf, cnt, buf, outPos using goCur.induct
    (litTable := litTable) (litLD := litLD) (maxBits := maxBits) (data := data)
    (maxOut := maxOut) (hsz := hsz) (hlp := hlp) with
  | case1 pos bitBuf cnt buf outPos hrc ih =>
    intro hinv cf c2 rp rb rc h; rw [goCur, dif_pos hrc] at h; exact ih hinv cf c2 rp rb rc h
  | case2 pos bitBuf cnt buf outPos hrc ent hlit hmax =>
    intro hinv cf c2 rp rb rc h; rw [goCur, dif_neg hrc, dif_pos hlit, if_pos hmax] at h
    exact absurd h (by simp)
  | case3 pos bitBuf cnt buf outPos hrc ent hlit hmax ih =>
    intro hinv cf c2 rp rb rc h; rw [goCur, dif_neg hrc, dif_pos hlit, if_neg hmax] at h
    have hltm : outPos.toNat < maxOut := Nat.not_le.mp hmax
    have hop1 : (outPos + 1).toNat = outPos.toNat + 1 := by
      rw [USize.toNat_add, USize.toNat_one]; apply Nat.mod_eq_of_lt
      exact USize.size_eq_two_pow ▸ (show outPos.toNat + 1 < USize.size by omega)
    exact ih (by omega) cf c2 rp rb rc h
  | case4 pos bitBuf cnt buf outPos hrc ent hlit e hde =>
    intro hinv cf c2 rp rb rc h; rw [goCur, dif_neg hrc, dif_neg hlit, hde] at h
    exact absurd h (by simp)
  | case5 pos bitBuf cnt buf outPos hrc ent hlit sym bb c' used hde hsym hmax =>
    intro hinv cf c2 rp rb rc h; rw [goCur, dif_neg hrc, dif_neg hlit, hde] at h
    simp only [] at h; rw [if_pos hsym, if_pos hmax] at h; exact absurd h (by simp)
  | case6 pos bitBuf cnt buf outPos hrc ent hlit cnt0 sym bb c' used hde hsym hmax hnp =>
    intro hinv cf c2 rp rb rc h; rw [goCur, dif_neg hrc, dif_neg hlit, hde] at h
    simp only [] at h; rw [if_pos hsym, if_neg hmax, dif_pos hnp] at h; exact absurd h (by simp)
  | case7 pos bitBuf cnt buf outPos hrc ent hlit cnt0 sym bb c' used hde hsym hmax hnp ih =>
    intro hinv cf c2 rp rb rc h; rw [goCur, dif_neg hrc, dif_neg hlit, hde] at h
    simp only [] at h; rw [if_pos hsym, if_neg hmax, dif_neg hnp] at h
    have hltm : outPos.toNat < maxOut := Nat.not_le.mp hmax
    have hop1 : (outPos + 1).toNat = outPos.toNat + 1 := by
      rw [USize.toNat_add, USize.toNat_one]; apply Nat.mod_eq_of_lt
      exact USize.size_eq_two_pow ▸ (show outPos.toNat + 1 < USize.size by omega)
    exact ih (by omega) cf c2 rp rb rc h
  | case8 pos bitBuf cnt buf outPos hrc ent hlit sym bb c' used hde hsym heob =>
    intro hinv cf c2 rp rb rc h; rw [goCur, dif_neg hrc, dif_neg hlit, hde] at h
    simp only [] at h; rw [if_neg hsym, if_pos heob] at h
    simp only [Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨_, hc2, _⟩ := h; subst hc2; exact hinv
  | case9 pos bitBuf cnt buf outPos hrc ent hlit sym bb c' used hde hsym hneob idx hidx =>
    intro hinv cf c2 rp rb rc h; rw [goCur, dif_neg hrc, dif_neg hlit, hde] at h
    simp only [] at h
    rw [if_neg hsym, if_neg hneob, dif_pos (show sym.toNat - 257 ≥ Inflate.lengthBase.size from hidx)] at h
    exact absurd h (by simp)
  | case10 pos bitBuf cnt buf outPos hrc ent hlit cnt0 sym bb c' used hde hsym hneob idx hh base ih =>
    intro hinv cf c2 rp rb rc h
    have hhc : ¬ sym.toNat - 257 ≥ Inflate.lengthBase.size := hh
    rw [goCur, dif_neg hrc, dif_neg hlit, hde] at h
    simp only [if_neg hsym, if_neg hneob, dif_neg hhc, bind, Except.bind] at h
    cases htb : InflateBuf.takeBits bb c'
        (Inflate.lengthExtra[sym.toNat - 257]'(by
          simp only [Inflate.lengthExtra_size]
          simp only [Inflate.lengthBase_size, ge_iff_le, Nat.not_le] at hhc; omega)).toNat with
    | error e => rw [htb] at h; exact absurd h (by simp)
    | ok pe =>
      obtain ⟨eb, bb2, c2'⟩ := pe; rw [htb] at h; simp only [] at h
      cases hde2 : HuffTree.decodeSymCanon distLD distTable maxBits bb2 c2' with
      | error e => rw [hde2] at h; exact absurd h (by simp)
      | ok pd =>
        obtain ⟨dsym, bb3, c3, dused⟩ := pd; rw [hde2] at h; simp only [] at h
        by_cases hdidx : dsym.toNat ≥ Inflate.distBase.size
        · rw [dif_pos hdidx] at h; exact absurd h (by simp)
        · rw [dif_neg hdidx] at h; try simp only [bind, Except.bind] at h
          cases htb2 : InflateBuf.takeBits bb3 c3
              (Inflate.distExtra[dsym.toNat]'(by
                try simp only [Inflate.distBase_size, ge_iff_le, Nat.not_le] at hdidx
                try simp only [Inflate.distExtra_size]
                omega)).toNat with
          | error e => rw [htb2] at h; exact absurd h (by simp)
          | ok pd2 =>
            obtain ⟨deb, bb4, c4⟩ := pd2; rw [htb2] at h; simp only [] at h
            by_cases hz : Inflate.distBase[dsym.toNat].toNat + deb = 0
            · rw [dif_pos hz] at h; exact absurd h (by simp)
            · rw [dif_neg hz] at h
              by_cases hds : Inflate.distBase[dsym.toNat].toNat + deb > outPos.toNat
              · rw [dif_pos hds] at h; exact absurd h (by simp)
              · rw [dif_neg hds] at h
                by_cases hmax : outPos.toNat + (Inflate.lengthBase[sym.toNat - 257].toNat + eb) > maxOut
                · rw [if_pos hmax] at h; exact absurd h (by simp)
                · rw [if_neg hmax] at h
                  by_cases hnp : cnt.toNat ≤ c4
                  · rw [dif_pos hnp] at h; exact absurd h (by simp)
                  · rw [dif_neg hnp] at h
                    have hle : outPos.toNat + (Inflate.lengthBase[sym.toNat - 257].toNat + eb) ≤ maxOut :=
                      Nat.not_lt.mp hmax
                    have hlenlt : Inflate.lengthBase[sym.toNat - 257].toNat + eb < USize.size :=
                      Nat.lt_of_le_of_lt (Nat.le_trans (Nat.le_add_left _ _) hle) hmo
                    have hadv : (outPos + (Inflate.lengthBase[sym.toNat - 257].toNat + eb).toUSize).toNat
                        = outPos.toNat + (Inflate.lengthBase[sym.toNat - 257].toNat + eb) := by
                      rw [USize.toNat_add, InflateBuf.toUSize_toNat_of_lt hlenlt]
                      apply Nat.mod_eq_of_lt
                      exact USize.size_eq_two_pow ▸ Nat.lt_of_le_of_lt hle hmo
                    exact ih eb dsym hdidx deb bb4 c4 hnp (by rw [hadv]; exact hle) cf c2 rp rb rc h

set_option maxRecDepth 8192 in
/-- **Reverse of `goCur_eq`**: whenever the write-once cursor `goCur` succeeds (and
    its final cursor `c2` fits the buffer — the exact-size regime), the reference
    `goTreeFreeU` on the logical prefix succeeds with the same tail bytes. Together
    with `goCur_eq` and determinism this pins down `goCur`-accepts ⟺
    `goTreeFreeU`-accepts, the soundness direction the fastloop needs. Same 10-case
    `goCur.induct`; the throw cases are `goCur`-contradictions (as in `goCur_size`),
    the recursive cases mirror `goCur_eq` with the write bridges applied to the goal. -/
theorem goCur_treeFree (litTable distTable : HuffTree.DecodeTable) (litLD distLD : HuffTree.LongDecode)
    (maxBits : Nat) (data : ByteArray) (maxOut : Nat) (hsz : data.size < USize.size)
    (hlp : litTable.packed.size = 2 ^ HuffTree.fastBits) (hmo : maxOut < USize.size) :
    ∀ (pos : USize) (bitBuf : UInt64) (cnt : USize) (buf : ByteArray) (outPos : USize),
    pos.toNat ≤ data.size → outPos.toNat ≤ buf.size → buf.size < USize.size →
    ∀ (cf : ByteArray) (c2 rp : USize) (rb : UInt64) (rc : USize),
    goCur litTable distTable litLD distLD maxBits data maxOut pos bitBuf cnt hsz hlp buf outPos
      = .ok (cf, c2, rp, rb, rc) → c2.toNat ≤ buf.size →
    goTreeFreeU litTable distTable litLD distLD maxBits data maxOut pos bitBuf cnt hsz hlp
        (buf.extract 0 outPos.toNat) = .ok (cf.extract 0 c2.toNat, rp, rb, rc) := by
  intro pos bitBuf cnt buf outPos
  induction pos, bitBuf, cnt, buf, outPos using goCur.induct
    (litTable := litTable) (litLD := litLD) (maxBits := maxBits) (data := data)
    (maxOut := maxOut) (hsz := hsz) (hlp := hlp) with
  | case1 pos bitBuf cnt buf outPos hrc ih =>
    intro hpos hout hbuf cf c2 rp rb rc h hc2
    have hpn : pos.toNat < data.size := by
      have h' := USize.lt_iff_toNat_lt.mp hrc.2; rwa [InflateBuf.toUSize_toNat_of_lt hsz] at h'
    have hpa : (pos + 1).toNat = pos.toNat + 1 := by
      rw [USize.toNat_add, USize.toNat_one]; apply Nat.mod_eq_of_lt
      exact USize.size_eq_two_pow ▸ (show pos.toNat + 1 < USize.size by omega)
    rw [goCur, dif_pos hrc] at h
    rw [goTreeFreeU, dif_pos hrc]
    exact ih (by rw [hpa]; omega) hout hbuf cf c2 rp rb rc h hc2
  | case2 pos bitBuf cnt buf outPos hrc ent hlit hmax =>
    intro hpos hout hbuf cf c2 rp rb rc h hc2
    rw [goCur, dif_neg hrc, dif_pos hlit, if_pos hmax] at h; exact absurd h (by simp)
  | case3 pos bitBuf cnt buf outPos hrc ent hlit hmax ih =>
    intro hpos hout hbuf cf c2 rp rb rc h hc2
    have hos : (buf.extract 0 outPos.toNat).size = outPos.toNat := by rw [ByteArray.size_extract]; omega
    have hltm : outPos.toNat < maxOut := Nat.not_le.mp hmax
    have hop1 : (outPos + 1).toNat = outPos.toNat + 1 := by
      rw [USize.toNat_add, USize.toNat_one]; apply Nat.mod_eq_of_lt
      exact USize.size_eq_two_pow ▸ (show outPos.toNat + 1 < USize.size by omega)
    rw [goCur, dif_neg hrc, dif_pos hlit, if_neg hmax] at h
    have hmn := goCur_outPos_mono litTable distTable litLD distLD maxBits data maxOut hsz hlp hmo
      _ _ _ _ _ cf c2 rp rb rc h
    have hlt : outPos.toNat < buf.size := by omega
    rw [goTreeFreeU, dif_neg hrc, dif_pos hlit, if_neg (by rw [hos]; exact hmax)]
    rw [← set!_extract_eq_push buf outPos.toNat _ hlt, ← hop1]
    exact ih hpos (by rw [ByteArray.size_set!, hop1]; omega) (by rw [ByteArray.size_set!]; exact hbuf)
      cf c2 rp rb rc h (by rw [ByteArray.size_set!]; exact hc2)
  | case4 pos bitBuf cnt buf outPos hrc ent hlit e hde =>
    intro hpos hout hbuf cf c2 rp rb rc h hc2
    rw [goCur, dif_neg hrc, dif_neg hlit, hde] at h; exact absurd h (by simp)
  | case5 pos bitBuf cnt buf outPos hrc ent hlit sym bb c' used hde hsym hmax =>
    intro hpos hout hbuf cf c2 rp rb rc h hc2
    rw [goCur, dif_neg hrc, dif_neg hlit, hde] at h
    simp only [] at h; rw [if_pos hsym, if_pos hmax] at h; exact absurd h (by simp)
  | case6 pos bitBuf cnt buf outPos hrc ent hlit cnt0 sym bb c' used hde hsym hmax hnp =>
    intro hpos hout hbuf cf c2 rp rb rc h hc2
    rw [goCur, dif_neg hrc, dif_neg hlit, hde] at h
    simp only [] at h; rw [if_pos hsym, if_neg hmax, dif_pos hnp] at h; exact absurd h (by simp)
  | case7 pos bitBuf cnt buf outPos hrc ent hlit cnt0 sym bb c' used hde hsym hmax hnp ih =>
    intro hpos hout hbuf cf c2 rp rb rc h hc2
    have hos : (buf.extract 0 outPos.toNat).size = outPos.toNat := by rw [ByteArray.size_extract]; omega
    have hltm : outPos.toNat < maxOut := Nat.not_le.mp hmax
    have hop1 : (outPos + 1).toNat = outPos.toNat + 1 := by
      rw [USize.toNat_add, USize.toNat_one]; apply Nat.mod_eq_of_lt
      exact USize.size_eq_two_pow ▸ (show outPos.toNat + 1 < USize.size by omega)
    rw [goCur, dif_neg hrc, dif_neg hlit, hde] at h
    simp only [] at h; rw [if_pos hsym, if_neg hmax, dif_neg hnp] at h
    have hmn := goCur_outPos_mono litTable distTable litLD distLD maxBits data maxOut hsz hlp hmo
      _ _ _ _ _ cf c2 rp rb rc h
    have hlt : outPos.toNat < buf.size := by omega
    rw [goTreeFreeU, dif_neg hrc, dif_neg hlit, hde]
    simp only []
    rw [if_pos hsym, if_neg (by rw [hos]; exact hmax), dif_neg hnp]
    rw [← set!_extract_eq_push buf outPos.toNat _ hlt, ← hop1]
    exact ih hpos (by rw [ByteArray.size_set!, hop1]; omega) (by rw [ByteArray.size_set!]; exact hbuf)
      cf c2 rp rb rc h (by rw [ByteArray.size_set!]; exact hc2)
  | case8 pos bitBuf cnt buf outPos hrc ent hlit sym bb c' used hde hsym heob =>
    intro hpos hout hbuf cf c2 rp rb rc h hc2
    rw [goCur, dif_neg hrc, dif_neg hlit, hde] at h
    simp only [] at h; rw [if_neg hsym, if_pos heob] at h
    simp only [Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := h
    rw [goTreeFreeU, dif_neg hrc, dif_neg hlit, hde]
    simp only []
    rw [if_neg hsym, if_pos heob]
  | case9 pos bitBuf cnt buf outPos hrc ent hlit sym bb c' used hde hsym hneob idx hidx =>
    intro hpos hout hbuf cf c2 rp rb rc h hc2
    rw [goCur, dif_neg hrc, dif_neg hlit, hde] at h
    simp only [] at h
    rw [if_neg hsym, if_neg hneob,
      dif_pos (show sym.toNat - 257 ≥ Inflate.lengthBase.size from hidx)] at h
    exact absurd h (by simp)
  | case10 pos bitBuf cnt buf outPos hrc ent hlit cnt0 sym bb c' used hde hsym hneob idx hh base ih =>
    intro hpos hout hbuf cf c2 rp rb rc h hc2
    have hos : (buf.extract 0 outPos.toNat).size = outPos.toNat := by rw [ByteArray.size_extract]; omega
    have hhc : ¬ sym.toNat - 257 ≥ Inflate.lengthBase.size := hh
    rw [goCur, dif_neg hrc, dif_neg hlit, hde] at h
    simp only [if_neg hsym, if_neg hneob, dif_neg hhc, bind, Except.bind] at h
    cases htb : InflateBuf.takeBits bb c'
        (Inflate.lengthExtra[sym.toNat - 257]'(by
          simp only [Inflate.lengthExtra_size]
          simp only [Inflate.lengthBase_size, ge_iff_le, Nat.not_le] at hhc; omega)).toNat with
    | error e => rw [htb] at h; exact absurd h (by simp)
    | ok pe =>
      obtain ⟨eb, bb2, c2'⟩ := pe; rw [htb] at h; simp only [] at h
      cases hde2 : HuffTree.decodeSymCanon distLD distTable maxBits bb2 c2' with
      | error e => rw [hde2] at h; exact absurd h (by simp)
      | ok pd =>
        obtain ⟨dsym, bb3, c3, dused⟩ := pd; rw [hde2] at h; simp only [] at h
        by_cases hdidx : dsym.toNat ≥ Inflate.distBase.size
        · rw [dif_pos hdidx] at h; exact absurd h (by simp)
        · rw [dif_neg hdidx] at h; try simp only [bind, Except.bind] at h
          cases htb2 : InflateBuf.takeBits bb3 c3
              (Inflate.distExtra[dsym.toNat]'(by
                try simp only [Inflate.distBase_size, ge_iff_le, Nat.not_le] at hdidx
                try simp only [Inflate.distExtra_size]
                omega)).toNat with
          | error e => rw [htb2] at h; exact absurd h (by simp)
          | ok pd2 =>
            obtain ⟨deb, bb4, c4⟩ := pd2; rw [htb2] at h; simp only [] at h
            by_cases hz : Inflate.distBase[dsym.toNat].toNat + deb = 0
            · rw [dif_pos hz] at h; exact absurd h (by simp)
            · rw [dif_neg hz] at h
              by_cases hds : Inflate.distBase[dsym.toNat].toNat + deb > outPos.toNat
              · rw [dif_pos hds] at h; exact absurd h (by simp)
              · rw [dif_neg hds] at h
                by_cases hmax : outPos.toNat + (Inflate.lengthBase[sym.toNat - 257].toNat + eb) > maxOut
                · rw [if_pos hmax] at h; exact absurd h (by simp)
                · rw [if_neg hmax] at h
                  by_cases hnp : cnt.toNat ≤ c4
                  · rw [dif_pos hnp] at h; exact absurd h (by simp)
                  · rw [dif_neg hnp] at h
                    have hd0 : 0 < Inflate.distBase[dsym.toNat].toNat + deb := Nat.pos_of_ne_zero hz
                    have hdle : Inflate.distBase[dsym.toNat].toNat + deb ≤ outPos.toNat := Nat.not_lt.mp hds
                    have hle : outPos.toNat + (Inflate.lengthBase[sym.toNat - 257].toNat + eb) ≤ maxOut :=
                      Nat.not_lt.mp hmax
                    have hlenlt : Inflate.lengthBase[sym.toNat - 257].toNat + eb < USize.size :=
                      Nat.lt_of_le_of_lt (Nat.le_trans (Nat.le_add_left _ _) hle) hmo
                    have hadv : (outPos + (Inflate.lengthBase[sym.toNat - 257].toNat + eb).toUSize).toNat
                        = outPos.toNat + (Inflate.lengthBase[sym.toNat - 257].toNat + eb) := by
                      rw [USize.toNat_add, InflateBuf.toUSize_toNat_of_lt hlenlt]
                      apply Nat.mod_eq_of_lt
                      exact USize.size_eq_two_pow ▸ Nat.lt_of_le_of_lt hle hmo
                    have hmn := goCur_outPos_mono litTable distTable litLD distLD maxBits data maxOut
                      hsz hlp hmo _ _ _ _ _ cf c2 rp rb rc h
                    have hlen : outPos.toNat + (Inflate.lengthBase[sym.toNat - 257].toNat + eb)
                        ≤ buf.size := by rw [← hadv]; exact Nat.le_trans hmn hc2
                    rw [goTreeFreeU, dif_neg hrc, dif_neg hlit, hde]
                    simp only [if_neg hsym, if_neg hneob, dif_neg hhc, bind, Except.bind]
                    rw [htb]; simp only []
                    rw [hde2]; simp only []
                    rw [dif_neg hdidx]; try simp only [bind, Except.bind]
                    rw [htb2]; simp only []
                    rw [dif_neg hz, dif_neg (by rw [hos]; exact hds),
                      if_neg (by rw [hos]; exact hmax), dif_neg hnp]
                    rw [← copyWithinAt_extract_eq_copyLoop buf outPos.toNat _ _ hd0 hdle hlen, ← hadv]
                    exact ih eb dsym hdidx deb bb4 c4 hnp hpos
                      (by rw [copyWithinAt_size, hadv]; exact hlen)
                      (by rw [copyWithinAt_size]; exact hbuf) cf c2 rp rb rc h
                      (by rw [copyWithinAt_size]; exact hc2)

/-! ### Stored-block bridge -/

/-- `getElem!` of a `ByteArray` append, split at the boundary. -/
private theorem getElem!_ba_append (a b : ByteArray) (j : Nat) :
    (a ++ b)[j]! = if j < a.size then a[j]! else b[j - a.size]! := by
  by_cases hj : j < a.size
  · rw [getElem!_pos (a ++ b) j (by rw [ByteArray.size_append]; omega),
      getElem!_pos a j hj, ByteArray.getElem_append_left hj, if_pos hj]
  · rw [if_neg hj]
    by_cases hj2 : j - a.size < b.size
    · rw [getElem!_pos (a ++ b) j (by rw [ByteArray.size_append]; omega),
        getElem!_pos b (j - a.size) hj2, ByteArray.getElem_append_right (by omega)]
    · rw [getElem!_neg (a ++ b) j (by rw [ByteArray.size_append]; omega),
        getElem!_neg b (j - a.size) hj2]

/-- `storedCopyLoop` preserves the buffer size (`set!` never grows). -/
@[simp] theorem storedCopyLoop_size (bytes : ByteArray) (outPos len : Nat) :
    ∀ (buf : ByteArray) (start : Nat),
    (InflateBuf.storedCopyLoop buf bytes outPos start len).size = buf.size := by
  intro buf start
  induction buf, start using InflateBuf.storedCopyLoop.induct (bytes := bytes)
    (outPos := outPos) (len := len) with
  | case1 buf start hlt ih => rw [InflateBuf.storedCopyLoop, if_pos hlt, ih, ByteArray.size_set!]
  | case2 buf start hge => rw [InflateBuf.storedCopyLoop, if_neg hge]

/-- **Content of the stored copy loop.** Slot `j` holds the copied byte
    `bytes[j - outPos]` inside the written window `[outPos+start, outPos+len)`,
    and the original buffer byte outside it. -/
theorem storedCopyLoop_getElem! (bytes : ByteArray) (outPos len : Nat) :
    ∀ (buf : ByteArray) (start j : Nat),
    (InflateBuf.storedCopyLoop buf bytes outPos start len)[j]!
      = if outPos + start ≤ j ∧ j < outPos + len ∧ j < buf.size then
          bytes[j - outPos]! else buf[j]! := by
  intro buf start j
  induction buf, start using InflateBuf.storedCopyLoop.induct (bytes := bytes)
    (outPos := outPos) (len := len) with
  | case1 buf start hlt ih =>
    rw [InflateBuf.storedCopyLoop, if_pos hlt, ih, ByteArray.getElem!_set!, ByteArray.size_set!]
    split
    · rename_i h; rw [if_pos ⟨by omega, h.2.1, h.2.2⟩]
    · rename_i h
      split
      · rename_i h2
        rw [if_pos ⟨by omega, by omega, by omega⟩, ByteArray.get!_eq_getElem!]
        congr 1; omega
      · rename_i h2
        rw [if_neg (fun hc => ?_)]
        rcases Nat.lt_or_ge (outPos + start) j with hgt | hle
        · exact h ⟨by omega, hc.2.1, hc.2.2⟩
        · exact h2 ⟨by omega, by omega⟩
  | case2 buf start hge =>
    rw [InflateBuf.storedCopyLoop, if_neg hge,
      if_neg (fun h => by have := h.1; have := h.2.1; omega)]

/-- **The stored-block write bridge.** Placing `bytes` at the cursor via
    `storedCopyLoop`, then extracting `[0, outPos+len)`, equals the reference's
    `buf.extract 0 outPos ++ bytes`. -/
theorem storedCopyLoop_extract (buf bytes : ByteArray) (outPos len : Nat)
    (hb : bytes.size = len) (hle : outPos + len ≤ buf.size) :
    (InflateBuf.storedCopyLoop buf bytes outPos 0 len).extract 0 (outPos + len)
      = buf.extract 0 outPos ++ bytes := by
  apply ByteArray.ext_getElem!
  · rw [ByteArray.size_extract, storedCopyLoop_size, ByteArray.size_append,
      ByteArray.size_extract]; omega
  · intro i hi
    rw [ByteArray.size_extract, storedCopyLoop_size] at hi
    rw [ByteArray.getElem!_extract _ 0 _ i (by rw [storedCopyLoop_size]; omega), Nat.zero_add,
      storedCopyLoop_getElem!, getElem!_ba_append, ByteArray.size_extract]
    by_cases hlt : i < outPos
    · rw [if_neg (fun h => by have := h.1; omega), if_pos (by omega),
        ByteArray.getElem!_extract _ 0 _ i (by omega), Nat.zero_add]
    · rw [if_pos ⟨by omega, by omega, by omega⟩, if_neg (by omega)]
      congr 1
      omega

/-- **Stored-block bridge.** A stored block placed at the cursor
    (`decodeStoredCur`) re-represents the reference stored block (`decodeStored`,
    which appends): the reads and `BitReader` bookkeeping are identical; the
    maximum-size guard aligns because `(buf.extract 0 outPos).size = outPos`; and
    the placed bytes are the reference bytes as a prefix (`storedCopyLoop_extract`). -/
theorem decodeStoredCur_eq (br : ZipCommon.BitReader) (buf : ByteArray) (outPos : Nat)
    (maxOut : Nat) (hout : outPos ≤ buf.size)
    (rf : ByteArray) (rbr : ZipCommon.BitReader)
    (href : Inflate.decodeStored br (buf.extract 0 outPos) maxOut = .ok (rf, rbr))
    (hroom : rf.size ≤ buf.size) :
    ∃ cf, InflateBuf.decodeStoredCur br buf outPos maxOut = .ok (cf, rf.size, rbr)
          ∧ cf.extract 0 rf.size = rf ∧ cf.size = buf.size := by
  have hos : (buf.extract 0 outPos).size = outPos := by rw [ByteArray.size_extract]; omega
  rw [Inflate.decodeStored] at href
  rw [InflateBuf.decodeStoredCur]
  cases h1 : br.readUInt16LE with
  | error e => simp [h1, bind, Except.bind] at href
  | ok r1 =>
    obtain ⟨len, br1⟩ := r1
    cases h2 : br1.readUInt16LE with
    | error e => simp [h1, h2, bind, Except.bind] at href
    | ok r2 =>
      obtain ⟨nlen, br2⟩ := r2
      simp only [h1, h2, bind, Except.bind, pure, Except.pure, hos] at href ⊢
      cases h3 : br2.readBytes len.toNat with
      | error e =>
        rw [h3] at href
        simp only [bind, Except.bind] at href
        split at href
        · exact absurd href (by simp)
        · split at href
          · exact absurd href (by simp)
          · exact absurd href (by simp)
      | ok r3 =>
        obtain ⟨bytes, br3⟩ := r3
        have hbsz : bytes.size = len.toNat := by
          rw [ZipCommon.BitReader.readBytes] at h3
          split at h3
          · exact absurd h3 (by simp)
          · simp only [Except.ok.injEq, Prod.mk.injEq] at h3
            obtain ⟨rfl, _⟩ := h3
            rw [ByteArray.size_extract]; omega
        rw [h3] at href
        simp only [bind, Except.bind] at href
        split at href
        · exact absurd href (by simp)
        · rename_i hc1
          split at href
          · exact absurd href (by simp)
          · rename_i hc2
            simp only [Except.ok.injEq, Prod.mk.injEq] at href
            obtain ⟨rfl, rfl⟩ := href
            have hrfsz : (buf.extract 0 outPos ++ bytes).size = outPos + len.toNat := by
              rw [ByteArray.size_append, hos, hbsz]
            simp only [hc1, hc2, h3, bind, Except.bind, ↓reduceIte] at ⊢
            refine ⟨InflateBuf.storedCopyLoop buf bytes outPos 0 len.toNat, ?_, ?_, ?_⟩
            · rw [if_neg (by decide : ¬(false = true)), hrfsz]
            · rw [hrfsz, storedCopyLoop_extract buf bytes outPos len.toNat hbsz (by omega)]
            · rw [storedCopyLoop_size]

theorem decodeHuffmanCurTables_eq (br : ZipCommon.BitReader) (buf : ByteArray) (outPos : Nat)
    (litTable distTable : HuffTree.DecodeTable) (litLD distLD : HuffTree.LongDecode) (maxOut : Nat)
    (hlp : litTable.packed.size = 2 ^ HuffTree.fastBits)
    (hds : br.data.size < USize.size) (hwf : br.bitOff < 8) (hbp : br.bitPos ≤ br.data.size * 8)
    (hout : outPos ≤ buf.size) (hbuf : buf.size < USize.size)
    (rf : ByteArray) (rbr : ZipCommon.BitReader)
    (href : InflateBuf.decodeHuffmanFastBufTables br (buf.extract 0 outPos)
              litTable distTable litLD distLD maxOut hlp = .ok (rf, rbr))
    (hroom : rf.size ≤ buf.size) :
    ∃ cf, InflateBuf.decodeHuffmanCurTables br buf outPos
            litTable distTable litLD distLD maxOut hlp = .ok (cf, rf.size, rbr)
          ∧ cf.extract 0 rf.size = rf ∧ cf.size = buf.size := by
  have hos : (buf.extract 0 outPos).size = outPos := by rw [ByteArray.size_extract]; omega
  have houtsz : outPos < USize.size := Nat.lt_of_le_of_lt hout hbuf
  have hsz : br.data.size.toUSize.toNat = br.data.size := InflateBuf.toUSize_toNat_of_lt hds
  -- Buffer invariant after the entry refill, giving the `pos ≤ size` bound `goCur_eq` needs.
  have hbpe : br.bitPos = br.pos * 8 + br.bitOff := rfl
  have hposle : br.pos ≤ br.data.size := by omega
  have hbc0 : BufCorr br.data (br.pos * 8) br.pos 0 0 :=
    ⟨by omega, hposle, by omega, by simp, fun j hj => absurd hj (Nat.not_lt_zero j)⟩
  rcases hrf : refill br.data br.pos 0 0 with ⟨pos0, bitBuf0, cnt0⟩
  obtain ⟨hbc1, hr1⟩ := refill_corr hbc0 hrf
  have hboff : br.bitOff ≤ cnt0 := by
    rcases hr1 with h56 | hpe
    · omega
    · have hs := hbc1.span; rw [hpe] at hs; omega
  have hbc2 := consume_corr hbc1 hboff (by omega)
  have hpos0le : pos0 ≤ br.data.size := hbc2.posLe
  have hpos0sz : pos0 < USize.size := Nat.lt_of_le_of_lt hpos0le hds
  have hrfsz : rf.size < USize.size := Nat.lt_of_le_of_lt hroom hbuf
  -- Unfold both decoders through the shared refill and the wide-buffer branch.
  rw [InflateBuf.decodeHuffmanFastBufTables, hrf] at href
  rw [InflateBuf.decodeHuffmanCurTables, hrf]
  simp only [hsz, ↓reduceDIte] at href ⊢
  -- The reference's `Except.map` of `goTreeFreeU`: it must be `.ok`.
  cases hgtf : goTreeFreeU litTable distTable litLD distLD 15 br.data maxOut
      pos0.toUSize (bitBuf0 >>> br.bitOff.toUInt64) (cnt0 - br.bitOff).toUSize
      (by rw [← hsz]; exact USize.toNat_lt_two_pow_numBits _) hlp (buf.extract 0 outPos) with
  | error e =>
    rw [hgtf] at href; simp only [Except.map, bind, Except.bind, reduceCtorEq] at href
  | ok res =>
    obtain ⟨o, p, b, c⟩ := res
    rw [hgtf] at href
    simp only [Except.map, bind, Except.bind, Except.ok.injEq, Prod.mk.injEq] at href
    obtain ⟨rfl, rfl⟩ := href
    -- Apply the cursor bisimulation to this block's tree-free decode.
    have hgc := goCur_eq litTable distTable litLD distLD 15 br.data maxOut hds hlp
      pos0.toUSize (bitBuf0 >>> br.bitOff.toUInt64) (cnt0 - br.bitOff).toUSize buf outPos.toUSize
      (by rw [InflateBuf.toUSize_toNat_of_lt hpos0sz]; exact hpos0le)
      (by rw [InflateBuf.toUSize_toNat_of_lt houtsz]; exact hout) hbuf
      o p b c
      (by rw [InflateBuf.toUSize_toNat_of_lt houtsz]; exact hgtf) hroom
    obtain ⟨cf, hcf, hext⟩ := hgc
    have hcsize := goCur_size litTable distTable litLD distLD 15 br.data maxOut hds hlp
      pos0.toUSize (bitBuf0 >>> br.bitOff.toUInt64) (cnt0 - br.bitOff).toUSize buf outPos.toUSize
      cf _ _ _ _ hcf
    refine ⟨cf, ?_, hext, hcsize⟩
    rw [hcf]
    simp only [bind, Except.bind, Except.ok.injEq, Prod.mk.injEq,
      InflateBuf.toUSize_toNat_of_lt hrfsz, and_self]

/-- **Reverse stored-block bridge.** Whenever the cursor stored block succeeds, the
    reference `decodeStored` on the logical prefix succeeds with the same bytes. -/
theorem decodeStoredCur_treeFree (br : ZipCommon.BitReader) (buf : ByteArray) (outPos maxOut : Nat)
    (hout : outPos ≤ buf.size) (cf : ByteArray) (op : Nat) (rbr : ZipCommon.BitReader)
    (h : InflateBuf.decodeStoredCur br buf outPos maxOut = .ok (cf, op, rbr)) (hop : op ≤ buf.size) :
    Inflate.decodeStored br (buf.extract 0 outPos) maxOut = .ok (cf.extract 0 op, rbr) := by
  have hos : (buf.extract 0 outPos).size = outPos := by rw [ByteArray.size_extract]; omega
  rw [InflateBuf.decodeStoredCur] at h
  rw [Inflate.decodeStored]
  cases h1 : br.readUInt16LE with
  | error e => simp [h1, bind, Except.bind] at h
  | ok r1 =>
    obtain ⟨len, br1⟩ := r1
    cases h2 : br1.readUInt16LE with
    | error e => simp [h1, h2, bind, Except.bind] at h
    | ok r2 =>
      obtain ⟨nlen, br2⟩ := r2
      cases h3 : br2.readBytes len.toNat with
      | error e =>
        simp only [h1, h2, h3, bind, Except.bind, pure, Except.pure] at h
        split at h
        · exact absurd h (by simp)
        · split at h <;> exact absurd h (by simp)
      | ok r3 =>
        obtain ⟨bytes, br3⟩ := r3
        have hbsz : bytes.size = len.toNat := by
          rw [ZipCommon.BitReader.readBytes] at h3
          split at h3
          · exact absurd h3 (by simp)
          · simp only [Except.ok.injEq, Prod.mk.injEq] at h3
            obtain ⟨rfl, _⟩ := h3; rw [ByteArray.size_extract]; omega
        simp only [h1, h2, h3, bind, Except.bind, pure, Except.pure] at h
        simp only [h1, h2, h3, bind, Except.bind, pure, Except.pure, hos]
        split at h
        · exact absurd h (by simp)
        · rename_i hc1
          split at h
          · exact absurd h (by simp)
          · rename_i hc2
            simp only [Except.ok.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, rfl, rfl⟩ := h
            rw [if_neg hc1, if_neg hc2,
              storedCopyLoop_extract buf bytes outPos len.toNat hbsz (by omega)]

/-- **Reverse Huffman-block bridge.** Whenever the cursor Huffman block succeeds
    (and its cursor fits the buffer), the reference `decodeHuffmanFastBufTables` on
    the logical prefix succeeds with the same bytes — carried straight through
    `goCur_treeFree`, no determinism. -/
theorem decodeHuffmanCurTables_treeFree (br : ZipCommon.BitReader) (buf : ByteArray) (outPos : Nat)
    (litTable distTable : HuffTree.DecodeTable) (litLD distLD : HuffTree.LongDecode) (maxOut : Nat)
    (hlp : litTable.packed.size = 2 ^ HuffTree.fastBits)
    (hds : br.data.size < USize.size) (hwf : br.bitOff < 8) (hbp : br.bitPos ≤ br.data.size * 8)
    (hout : outPos ≤ buf.size) (hbuf : buf.size < USize.size) (hmo : maxOut < USize.size)
    (cf : ByteArray) (op : Nat) (rbr : ZipCommon.BitReader)
    (h : InflateBuf.decodeHuffmanCurTables br buf outPos litTable distTable litLD distLD maxOut hlp
          = .ok (cf, op, rbr)) (hop : op ≤ buf.size) :
    InflateBuf.decodeHuffmanFastBufTables br (buf.extract 0 outPos)
        litTable distTable litLD distLD maxOut hlp = .ok (cf.extract 0 op, rbr) := by
  have hos : (buf.extract 0 outPos).size = outPos := by rw [ByteArray.size_extract]; omega
  have houtsz : outPos < USize.size := Nat.lt_of_le_of_lt hout hbuf
  have hsz : br.data.size.toUSize.toNat = br.data.size := InflateBuf.toUSize_toNat_of_lt hds
  have hbpe : br.bitPos = br.pos * 8 + br.bitOff := rfl
  have hposle : br.pos ≤ br.data.size := by omega
  have hbc0 : BufCorr br.data (br.pos * 8) br.pos 0 0 :=
    ⟨by omega, hposle, by omega, by simp, fun j hj => absurd hj (Nat.not_lt_zero j)⟩
  rcases hrf : refill br.data br.pos 0 0 with ⟨pos0, bitBuf0, cnt0⟩
  obtain ⟨hbc1, hr1⟩ := refill_corr hbc0 hrf
  have hboff : br.bitOff ≤ cnt0 := by
    rcases hr1 with h56 | hpe
    · omega
    · have hs := hbc1.span; rw [hpe] at hs; omega
  have hbc2 := consume_corr hbc1 hboff (by omega)
  have hpos0le : pos0 ≤ br.data.size := hbc2.posLe
  have hpos0sz : pos0 < USize.size := Nat.lt_of_le_of_lt hpos0le hds
  rw [InflateBuf.decodeHuffmanCurTables, hrf] at h
  rw [InflateBuf.decodeHuffmanFastBufTables, hrf]
  simp only [hsz, ↓reduceDIte] at h ⊢
  cases hgc : goCur litTable distTable litLD distLD 15 br.data maxOut
      pos0.toUSize (bitBuf0 >>> br.bitOff.toUInt64) (cnt0 - br.bitOff).toUSize
      (by rw [← hsz]; exact USize.toNat_lt_two_pow_numBits _) hlp buf outPos.toUSize with
  | error e => rw [hgc] at h; simp only [bind, Except.bind, reduceCtorEq] at h
  | ok res =>
    obtain ⟨co, cop, cpos, cbb, ccnt⟩ := res
    rw [hgc] at h
    simp only [bind, Except.bind, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    have htf := goCur_treeFree litTable distTable litLD distLD 15 br.data maxOut hds hlp hmo
      pos0.toUSize (bitBuf0 >>> br.bitOff.toUInt64) (cnt0 - br.bitOff).toUSize buf outPos.toUSize
      (by rw [InflateBuf.toUSize_toNat_of_lt hpos0sz]; exact hpos0le)
      (by rw [InflateBuf.toUSize_toNat_of_lt houtsz]; exact hout) hbuf
      co cop cpos cbb ccnt hgc hop
    rw [InflateBuf.toUSize_toNat_of_lt houtsz] at htf
    rw [htf]
    simp only [Except.map, bind, Except.bind, Except.ok.injEq, Prod.mk.injEq, and_self]

/-- The cursor stored block never moves the cursor backward. -/
theorem decodeStoredCur_outPos_mono {br : ZipCommon.BitReader} {buf : ByteArray} {outPos maxOut : Nat}
    {cf : ByteArray} {op : Nat} {rbr : ZipCommon.BitReader}
    (h : InflateBuf.decodeStoredCur br buf outPos maxOut = .ok (cf, op, rbr)) : outPos ≤ op := by
  rw [InflateBuf.decodeStoredCur] at h
  cases h1 : br.readUInt16LE with
  | error e => simp [h1, bind, Except.bind] at h
  | ok r1 =>
    obtain ⟨len, br1⟩ := r1
    cases h2 : br1.readUInt16LE with
    | error e => simp [h1, h2, bind, Except.bind] at h
    | ok r2 =>
      obtain ⟨nlen, br2⟩ := r2
      cases h3 : br2.readBytes len.toNat with
      | error e =>
        simp only [h1, h2, h3, bind, Except.bind, pure, Except.pure] at h
        split at h
        · exact absurd h (by simp)
        · split at h <;> exact absurd h (by simp)
      | ok r3 =>
        obtain ⟨bytes, br3⟩ := r3
        simp only [h1, h2, h3, bind, Except.bind, pure, Except.pure] at h
        split at h
        · exact absurd h (by simp)
        · split at h
          · exact absurd h (by simp)
          · simp only [Except.ok.injEq, Prod.mk.injEq] at h
            obtain ⟨_, rfl, _⟩ := h; omega

/-- The cursor Huffman block never moves the cursor backward (via `goCur_outPos_mono`). -/
theorem decodeHuffmanCurTables_outPos_mono {br : ZipCommon.BitReader} {buf : ByteArray} {outPos : Nat}
    {litTable distTable : HuffTree.DecodeTable} {litLD distLD : HuffTree.LongDecode} {maxOut : Nat}
    {hlp : litTable.packed.size = 2 ^ HuffTree.fastBits}
    (hds : br.data.size < USize.size) (hmo : maxOut < USize.size) (houtsz : outPos < USize.size)
    {cf : ByteArray} {op : Nat} {rbr : ZipCommon.BitReader}
    (h : InflateBuf.decodeHuffmanCurTables br buf outPos litTable distTable litLD distLD maxOut hlp
          = .ok (cf, op, rbr)) : outPos ≤ op := by
  have hsz : br.data.size.toUSize.toNat = br.data.size := InflateBuf.toUSize_toNat_of_lt hds
  rw [InflateBuf.decodeHuffmanCurTables] at h
  rcases hrf : refill br.data br.pos 0 0 with ⟨pos0, bitBuf0, cnt0⟩
  rw [hrf] at h
  simp only [hsz, ↓reduceDIte] at h
  cases hgc : goCur litTable distTable litLD distLD 15 br.data maxOut
      pos0.toUSize (bitBuf0 >>> br.bitOff.toUInt64) (cnt0 - br.bitOff).toUSize
      (by rw [← hsz]; exact USize.toNat_lt_two_pow_numBits _) hlp buf outPos.toUSize with
  | error e => rw [hgc] at h; simp only [bind, Except.bind, reduceCtorEq] at h
  | ok res =>
    obtain ⟨co, cop, cpos, cbb, ccnt⟩ := res
    rw [hgc] at h
    simp only [bind, Except.bind, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨_, rfl, _⟩ := h
    have hmn := goCur_outPos_mono litTable distTable litLD distLD 15 br.data maxOut
      (by rw [← hsz]; exact USize.toNat_lt_two_pow_numBits _) hlp hmo
      _ _ _ _ _ co cop cpos cbb ccnt hgc
    rwa [InflateBuf.toUSize_toNat_of_lt houtsz] at hmn

/-- The cursor stored block keeps the cursor in the output budget. -/
theorem decodeStoredCur_outPos_le_maxOut {br : ZipCommon.BitReader} {buf : ByteArray}
    {outPos maxOut : Nat} {cf : ByteArray} {op : Nat} {rbr : ZipCommon.BitReader}
    (h : InflateBuf.decodeStoredCur br buf outPos maxOut = .ok (cf, op, rbr)) : op ≤ maxOut := by
  rw [InflateBuf.decodeStoredCur] at h
  cases h1 : br.readUInt16LE with
  | error e => simp [h1, bind, Except.bind] at h
  | ok r1 =>
    obtain ⟨len, br1⟩ := r1
    cases h2 : br1.readUInt16LE with
    | error e => simp [h1, h2, bind, Except.bind] at h
    | ok r2 =>
      obtain ⟨nlen, br2⟩ := r2
      cases h3 : br2.readBytes len.toNat with
      | error e =>
        simp only [h1, h2, h3, bind, Except.bind, pure, Except.pure] at h
        split at h
        · exact absurd h (by simp)
        · split at h <;> exact absurd h (by simp)
      | ok r3 =>
        obtain ⟨bytes, br3⟩ := r3
        simp only [h1, h2, h3, bind, Except.bind, pure, Except.pure] at h
        split at h
        · exact absurd h (by simp)
        · split at h
          · exact absurd h (by simp)
          · simp only [Except.ok.injEq, Prod.mk.injEq] at h
            obtain ⟨_, rfl, _⟩ := h; omega

/-- The cursor Huffman block keeps the cursor in the output budget (via
    `goCur_outPos_le_maxOut`). -/
theorem decodeHuffmanCurTables_outPos_le_maxOut {br : ZipCommon.BitReader} {buf : ByteArray}
    {outPos : Nat} {litTable distTable : HuffTree.DecodeTable} {litLD distLD : HuffTree.LongDecode}
    {maxOut : Nat} {hlp : litTable.packed.size = 2 ^ HuffTree.fastBits}
    (hds : br.data.size < USize.size) (hmo : maxOut < USize.size) (houtsz : outPos < USize.size)
    (hinv : outPos ≤ maxOut) {cf : ByteArray} {op : Nat} {rbr : ZipCommon.BitReader}
    (h : InflateBuf.decodeHuffmanCurTables br buf outPos litTable distTable litLD distLD maxOut hlp
          = .ok (cf, op, rbr)) : op ≤ maxOut := by
  have hsz : br.data.size.toUSize.toNat = br.data.size := InflateBuf.toUSize_toNat_of_lt hds
  rw [InflateBuf.decodeHuffmanCurTables] at h
  rcases hrf : refill br.data br.pos 0 0 with ⟨pos0, bitBuf0, cnt0⟩
  rw [hrf] at h
  simp only [hsz, ↓reduceDIte] at h
  cases hgc : goCur litTable distTable litLD distLD 15 br.data maxOut
      pos0.toUSize (bitBuf0 >>> br.bitOff.toUInt64) (cnt0 - br.bitOff).toUSize
      (by rw [← hsz]; exact USize.toNat_lt_two_pow_numBits _) hlp buf outPos.toUSize with
  | error e => rw [hgc] at h; simp only [bind, Except.bind, reduceCtorEq] at h
  | ok res =>
    obtain ⟨co, cop, cpos, cbb, ccnt⟩ := res
    rw [hgc] at h
    simp only [bind, Except.bind, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨_, rfl, _⟩ := h
    exact goCur_outPos_le_maxOut litTable distTable litLD distLD 15 br.data maxOut
      (by rw [← hsz]; exact USize.toNat_lt_two_pow_numBits _) hlp hmo
      _ _ _ _ _ (by rw [InflateBuf.toUSize_toNat_of_lt houtsz]; exact hinv)
      co cop cpos cbb ccnt hgc

/-- `readBytes` preserves the underlying data (mirrors the private `readBytes_inv`). -/
theorem readBytes_data {br br' : ZipCommon.BitReader} {n : Nat} {bytes : ByteArray}
    (h : br.readBytes n = .ok (bytes, br')) : br'.data = br.data := by
  simp only [ZipCommon.BitReader.readBytes, ZipCommon.BitReader.alignToByte] at h
  split at h
  · split at h
    · exact nomatch h
    · simp only [Except.ok.injEq, Prod.mk.injEq] at h; obtain ⟨_, rfl⟩ := h; rfl
  · split at h
    · exact nomatch h
    · simp only [Except.ok.injEq, Prod.mk.injEq] at h; obtain ⟨_, rfl⟩ := h; rfl

/-- The cursor stored block preserves the underlying data. -/
theorem decodeStoredCur_data {br : ZipCommon.BitReader} {buf : ByteArray} {outPos maxOut : Nat}
    {cf : ByteArray} {op : Nat} {cbr : ZipCommon.BitReader}
    (h : InflateBuf.decodeStoredCur br buf outPos maxOut = .ok (cf, op, cbr)) : cbr.data = br.data := by
  rw [InflateBuf.decodeStoredCur] at h
  cases h1 : br.readUInt16LE with
  | error e => simp [h1, bind, Except.bind] at h
  | ok r1 =>
    obtain ⟨len, br1⟩ := r1
    cases h2 : br1.readUInt16LE with
    | error e => simp [h1, h2, bind, Except.bind] at h
    | ok r2 =>
      obtain ⟨nlen, br2⟩ := r2
      cases h3 : br2.readBytes len.toNat with
      | error e =>
        simp only [h1, h2, h3, bind, Except.bind, pure, Except.pure] at h
        split at h
        · exact absurd h (by simp)
        · split at h <;> exact absurd h (by simp)
      | ok r3 =>
        obtain ⟨bytes, br3⟩ := r3
        simp only [h1, h2, h3, bind, Except.bind, pure, Except.pure] at h
        split at h
        · exact absurd h (by simp)
        · split at h
          · exact absurd h (by simp)
          · simp only [Except.ok.injEq, Prod.mk.injEq] at h
            obtain ⟨_, _, rfl⟩ := h
            rw [readBytes_data h3, Deflate.Correctness.readUInt16LE_data br1 nlen br2 h2,
              Deflate.Correctness.readUInt16LE_data br len br1 h1]

/-- The cursor Huffman block preserves the underlying data (the result `BitReader`
    is built on `br.data`). -/
theorem decodeHuffmanCurTables_data {br : ZipCommon.BitReader} {buf : ByteArray} {outPos : Nat}
    {litTable distTable : HuffTree.DecodeTable} {litLD distLD : HuffTree.LongDecode} {maxOut : Nat}
    {hlp : litTable.packed.size = 2 ^ HuffTree.fastBits} (hds : br.data.size < USize.size)
    {cf : ByteArray} {op : Nat} {cbr : ZipCommon.BitReader}
    (h : InflateBuf.decodeHuffmanCurTables br buf outPos litTable distTable litLD distLD maxOut hlp
          = .ok (cf, op, cbr)) : cbr.data = br.data := by
  have hsz : br.data.size.toUSize.toNat = br.data.size := InflateBuf.toUSize_toNat_of_lt hds
  rw [InflateBuf.decodeHuffmanCurTables] at h
  rcases hrf : refill br.data br.pos 0 0 with ⟨pos0, bitBuf0, cnt0⟩
  rw [hrf] at h
  simp only [hsz, ↓reduceDIte] at h
  cases hgc : goCur litTable distTable litLD distLD 15 br.data maxOut
      pos0.toUSize (bitBuf0 >>> br.bitOff.toUInt64) (cnt0 - br.bitOff).toUSize
      (by rw [← hsz]; exact USize.toNat_lt_two_pow_numBits _) hlp buf outPos.toUSize with
  | error e => rw [hgc] at h; simp only [bind, Except.bind, reduceCtorEq] at h
  | ok res =>
    obtain ⟨co, cop, cpos, cbb, ccnt⟩ := res
    rw [hgc] at h
    simp only [bind, Except.bind, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨_, _, hcbr⟩ := h
    rw [← hcbr]

/-! ### Reference-loop output monotonicity (for the loop-lift room bound) -/

/-- One Huffman block never shrinks the output (via `goTreeFreeU_size_mono`). -/
theorem decodeHuffmanFastBufTables_size_mono (br : ZipCommon.BitReader) (output : ByteArray)
    (litTable distTable : HuffTree.DecodeTable) (litLD distLD : HuffTree.LongDecode) (maxOut : Nat)
    (hlp : litTable.packed.size = 2 ^ HuffTree.fastBits)
    (hds : br.data.size < USize.size) (hwf : br.bitOff < 8) (hbp : br.bitPos ≤ br.data.size * 8)
    (rf : ByteArray) (rbr : ZipCommon.BitReader)
    (href : InflateBuf.decodeHuffmanFastBufTables br output litTable distTable litLD distLD maxOut hlp
      = .ok (rf, rbr)) :
    output.size ≤ rf.size := by
  have hsz : br.data.size.toUSize.toNat = br.data.size := InflateBuf.toUSize_toNat_of_lt hds
  have hbpe : br.bitPos = br.pos * 8 + br.bitOff := rfl
  have hposle : br.pos ≤ br.data.size := by omega
  have hbc0 : BufCorr br.data (br.pos * 8) br.pos 0 0 :=
    ⟨by omega, hposle, by omega, by simp, fun j hj => absurd hj (Nat.not_lt_zero j)⟩
  rcases hrf : refill br.data br.pos 0 0 with ⟨pos0, bitBuf0, cnt0⟩
  obtain ⟨hbc1, hr1⟩ := refill_corr hbc0 hrf
  have hboff : br.bitOff ≤ cnt0 := by
    rcases hr1 with h56 | hpe
    · omega
    · have hs := hbc1.span; rw [hpe] at hs; omega
  have hbc2 := consume_corr hbc1 hboff (by omega)
  have hpos0le : pos0 ≤ br.data.size := hbc2.posLe
  have hpos0sz : pos0 < USize.size := Nat.lt_of_le_of_lt hpos0le hds
  rw [InflateBuf.decodeHuffmanFastBufTables, hrf] at href
  simp only [hsz, ↓reduceDIte] at href
  cases hgtf : goTreeFreeU litTable distTable litLD distLD 15 br.data maxOut
      pos0.toUSize (bitBuf0 >>> br.bitOff.toUInt64) (cnt0 - br.bitOff).toUSize
      (by rw [← hsz]; exact USize.toNat_lt_two_pow_numBits _) hlp output with
  | error e => rw [hgtf] at href; simp only [Except.map, bind, Except.bind, reduceCtorEq] at href
  | ok res =>
    obtain ⟨o, p, b, c⟩ := res
    rw [hgtf] at href
    simp only [Except.map, bind, Except.bind, Except.ok.injEq, Prod.mk.injEq] at href
    obtain ⟨rfl, rfl⟩ := href
    exact goTreeFreeU_size_mono litTable distTable litLD distLD 15 br.data maxOut hds hlp
      pos0.toUSize (bitBuf0 >>> br.bitOff.toUInt64) (cnt0 - br.bitOff).toUSize output o p b c
      (by rw [InflateBuf.toUSize_toNat_of_lt hpos0sz]; exact hpos0le) hgtf

/-- Peel a successful monadic bind. -/
private theorem bindOk' {α β} {e : Except String α} {f : α → Except String β} {r : β}
    (h : (e >>= f) = .ok r) : ∃ a, e = .ok a ∧ f a = .ok r := by
  cases e with
  | error _ => simp [bind, Except.bind] at h
  | ok a => exact ⟨a, rfl, h⟩

/-- A stored block never shrinks the output (it appends the raw bytes). -/
theorem decodeStored_size_mono (br : ZipCommon.BitReader) (output : ByteArray) (maxOut : Nat)
    (rf : ByteArray) (rbr : ZipCommon.BitReader)
    (href : Inflate.decodeStored br output maxOut = .ok (rf, rbr)) :
    output.size ≤ rf.size := by
  rw [Inflate.decodeStored] at href
  cases h1 : br.readUInt16LE with
  | error e => simp [h1, bind, Except.bind] at href
  | ok r1 =>
    obtain ⟨len, br1⟩ := r1
    cases h2 : br1.readUInt16LE with
    | error e => simp [h1, h2, bind, Except.bind] at href
    | ok r2 =>
      obtain ⟨nlen, br2⟩ := r2
      simp only [h1, h2, bind, Except.bind, pure, Except.pure] at href
      cases h3 : br2.readBytes len.toNat with
      | error e =>
        rw [h3] at href; simp only [bind, Except.bind] at href
        split at href
        · exact absurd href (by simp)
        · split at href
          · exact absurd href (by simp)
          · exact absurd href (by simp)
      | ok r3 =>
        obtain ⟨bytes, br3⟩ := r3
        rw [h3] at href
        simp only [bind, Except.bind] at href
        split at href
        · exact absurd href (by simp)
        · split at href
          · exact absurd href (by simp)
          · simp only [Except.ok.injEq, Prod.mk.injEq] at href
            obtain ⟨rfl, rfl⟩ := href
            rw [ByteArray.size_append]; omega

/-- One Huffman block leaves the reader byte-fielded (`bitOff < 8`) on the same
    data. -/
theorem decodeHuffmanFastBufTables_br (br : ZipCommon.BitReader) (output : ByteArray)
    (litTable distTable : HuffTree.DecodeTable) (litLD distLD : HuffTree.LongDecode) (maxOut : Nat)
    (hlp : litTable.packed.size = 2 ^ HuffTree.fastBits) (hds : br.data.size < USize.size)
    (rf : ByteArray) (rbr : ZipCommon.BitReader)
    (href : InflateBuf.decodeHuffmanFastBufTables br output litTable distTable litLD distLD maxOut hlp
      = .ok (rf, rbr)) :
    rbr.data = br.data ∧ rbr.bitOff < 8 := by
  have hsz : br.data.size.toUSize.toNat = br.data.size := InflateBuf.toUSize_toNat_of_lt hds
  rcases hrf : refill br.data br.pos 0 0 with ⟨pos0, bitBuf0, cnt0⟩
  rw [InflateBuf.decodeHuffmanFastBufTables, hrf] at href
  simp only [hsz, ↓reduceDIte] at href
  cases hgtf : goTreeFreeU litTable distTable litLD distLD 15 br.data maxOut
      pos0.toUSize (bitBuf0 >>> br.bitOff.toUInt64) (cnt0 - br.bitOff).toUSize
      (by rw [← hsz]; exact USize.toNat_lt_two_pow_numBits _) hlp output with
  | error e => rw [hgtf] at href; simp only [Except.map, bind, Except.bind, reduceCtorEq] at href
  | ok res =>
    obtain ⟨o, p, b, c⟩ := res
    rw [hgtf] at href
    simp only [Except.map, bind, Except.bind, Except.ok.injEq, Prod.mk.injEq] at href
    obtain ⟨_, rfl⟩ := href
    exact ⟨rfl, Nat.mod_lt _ (by omega)⟩

/-- **Reference block loop monotonicity.** `inflateLoopTreeFree` never shrinks the
    output — each block appends (stored) or grows through `goTreeFreeU`
    (`goTreeFreeU_size_mono`). Threads `bitOff < 8` (each decoder byte-fields the
    reader) and the `bitPos` bound (the loop's own recursion guard). -/
theorem inflateLoopTreeFree_size_mono (maxOut dataSize : Nat)
    (hdd : dataSize < USize.size) :
    ∀ (br : ZipCommon.BitReader) (output rf : ByteArray) (endPos : Nat),
    br.bitPos ≤ br.data.size * 8 → br.data.size = dataSize →
    Inflate.inflateLoopTreeFree br output maxOut dataSize = .ok (rf, endPos) →
    output.size ≤ rf.size := by
  intro br output
  induction br, output using Inflate.inflateLoopTreeFree.induct (dataSize := dataSize) with
  | case1 br output ih =>
    intro rf endPos hbp hds href
    rw [Inflate.inflateLoopTreeFree] at href
    obtain ⟨p1, hrb1, href⟩ := bindOk' href; obtain ⟨bfinal, br₁⟩ := p1; simp only [] at href
    obtain ⟨p2, hrb2, href⟩ := bindOk' href; obtain ⟨btype, br₂⟩ := p2; simp only [] at href
    have hbo₂ : br₂.bitOff < 8 := InflateBuf.readBits_bitOff_lt_pos (by omega) hrb2
    have hple : br.pos ≤ br.data.size := by
      have := hbp; simp only [ZipCommon.BitReader.bitPos] at this; omega
    have hpos : br.bitOff = 0 ∨ br.pos < br.data.size := by
      have := hbp; simp only [ZipCommon.BitReader.bitPos] at this
      rcases Nat.lt_or_ge br.pos br.data.size with h | h
      · exact Or.inr h
      · exact Or.inl (by omega)
    obtain ⟨_, hp₁, hl₁⟩ := ZipCommon.readBits_inv br br₁ 1 bfinal hrb1 hpos hple
    obtain ⟨hd₂, hp₂, hl₂⟩ := ZipCommon.readBits_inv br₁ br₂ 2 btype hrb2 hp₁ hl₁
    have hdata₂ : br₂.data.size = dataSize := by
      rw [ZipCommon.readBits_data_eq br₁ br₂ 2 btype hrb2,
        ZipCommon.readBits_data_eq br br₁ 1 bfinal hrb1]; exact hds
    have hbp₂ : br₂.bitPos ≤ br₂.data.size * 8 := by
      simp only [ZipCommon.BitReader.bitPos]; rcases hp₂ with h' | h' <;> omega
    -- one block, then the bfinal / progress / recurse tail
    have htail : ∀ (output' : ByteArray) (br' : ZipCommon.BitReader),
        output.size ≤ output'.size → br'.data.size = dataSize →
        (if bfinal == 1 then pure (output', br'.alignToByte.pos)
         else if _h : br'.bitPos ≤ br.bitPos then throw "Inflate: no progress in inflate loop"
              else if _h : dataSize * 8 < br'.bitPos then throw "Inflate: bit position out of range"
              else Inflate.inflateLoopTreeFree br' output' maxOut dataSize) = .ok (rf, endPos) →
        output.size ≤ rf.size := by
      intro output' br' hmono hds' ht
      by_cases hbf : (bfinal == 1) = true
      · rw [if_pos hbf] at ht; simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at ht
        obtain ⟨rfl, _⟩ := ht; exact hmono
      · rw [if_neg hbf] at ht
        by_cases hg1 : br'.bitPos ≤ br.bitPos
        · rw [dif_pos hg1] at ht; exact absurd ht (by simp)
        · rw [dif_neg hg1] at ht
          by_cases hg2 : dataSize * 8 < br'.bitPos
          · rw [dif_pos hg2] at ht; exact absurd ht (by simp)
          · rw [dif_neg hg2] at ht
            exact Nat.le_trans hmono (ih output' br' hg1 hg2 rf endPos (by rw [hds']; omega) hds' ht)
    have hbtv : btype = 0 ∨ btype = 1 ∨ btype = 2 ∨ btype = 3 := by
      have hb4 : btype.toNat < 4 := Inflate.readBits_lt (n := 2) (by omega) hrb2
      rcases (show btype.toNat = 0 ∨ btype.toNat = 1 ∨ btype.toNat = 2 ∨ btype.toNat = 3 from by omega)
        with h' | h' | h' | h'
      · exact Or.inl (UInt32.toNat_inj.mp (by rw [h']; rfl))
      · exact Or.inr (Or.inl (UInt32.toNat_inj.mp (by rw [h']; rfl)))
      · exact Or.inr (Or.inr (Or.inl (UInt32.toNat_inj.mp (by rw [h']; rfl))))
      · exact Or.inr (Or.inr (Or.inr (UInt32.toNat_inj.mp (by rw [h']; rfl))))
    simp only [bind, Except.bind] at href
    rcases hbtv with rfl | rfl | rfl | rfl
    · -- stored
      obtain ⟨pb, hblock, htl⟩ := bindOk' href; obtain ⟨output', br'⟩ := pb
      obtain ⟨hd', _, _⟩ := Zip.Native.decodeStored_inv br₂ br' output output' maxOut hblock
      simp only [] at htl
      exact htail output' br' (decodeStored_size_mono br₂ output maxOut output' br' hblock)
        (by rw [hd']; exact hdata₂) htl
    · -- fixed Huffman
      obtain ⟨pb, hblock, htl⟩ := bindOk' href; obtain ⟨output', br'⟩ := pb
      rw [Inflate.decodeHuffmanFastBufFixed] at hblock
      have hbr := decodeHuffmanFastBufTables_br br₂ output _ _ _ _ maxOut _
        (by rw [hdata₂]; exact hdd) output' br' hblock
      have hmn := decodeHuffmanFastBufTables_size_mono br₂ output _ _ _ _ maxOut _
        (by rw [hdata₂]; exact hdd) hbo₂ hbp₂ output' br' hblock
      simp only [] at htl
      exact htail output' br' hmn (by rw [hbr.1]; exact hdata₂) htl
    · -- dynamic Huffman
      obtain ⟨pdt, hdt, href⟩ := bindOk' href; obtain ⟨litLens, distLens, br₃⟩ := pdt; try simp only [] at href
      obtain ⟨pb, hblock, htl⟩ := bindOk' href; obtain ⟨output', br'⟩ := pb
      obtain ⟨hdyntrees, _, _, _, _⟩ := Inflate.decodeDynamicTrees_of_lengthsOnly hdt
      obtain ⟨hd₃, hp₃, hl₃⟩ := Zip.Native.decodeDynamicTrees_inv br₂ br₃ _ _ hdyntrees hp₂ hl₂
      have hbo₃ := InflateBuf.decodeDynamicTrees_bitOff_pres hbo₂ hdyntrees
      have hdata₃ : br₃.data.size = dataSize := by rw [hd₃]; exact hdata₂
      have hbp₃ : br₃.bitPos ≤ br₃.data.size * 8 := by
        simp only [ZipCommon.BitReader.bitPos]; rcases hp₃ with h' | h' <;> omega
      rw [InflateBuf.decodeHuffmanFastBufTreeFree] at hblock
      have hbr := decodeHuffmanFastBufTables_br br₃ output _ _ _ _ maxOut _
        (by rw [hdata₃]; exact hdd) output' br' hblock
      have hmn := decodeHuffmanFastBufTables_size_mono br₃ output _ _ _ _ maxOut _
        (by rw [hdata₃]; exact hdd) hbo₃ hbp₃ output' br' hblock
      simp only [] at htl
      exact htail output' br' hmn (by rw [hbr.1]; exact hdata₃) htl
    · -- reserved
      exact absurd href (by simp [bind, Except.bind])

/-- `decodeStoredCur` preserves the buffer size (it only `set!`s the raw bytes in place). -/
theorem decodeStoredCur_size {br : ZipCommon.BitReader} {output : ByteArray} {outPos maxOut : Nat}
    {out : ByteArray} {p : Nat} {br' : ZipCommon.BitReader}
    (h : InflateBuf.decodeStoredCur br output outPos maxOut = .ok (out, p, br')) :
    out.size = output.size := by
  rw [InflateBuf.decodeStoredCur] at h
  cases h1 : br.readUInt16LE with
  | error e => simp [h1, bind, Except.bind] at h
  | ok r1 =>
    obtain ⟨len, br1⟩ := r1
    cases h2 : br1.readUInt16LE with
    | error e => simp [h1, h2, bind, Except.bind] at h
    | ok r2 =>
      obtain ⟨nlen, br2⟩ := r2
      cases h3 : br2.readBytes len.toNat with
      | error e =>
        simp only [h1, h2, h3, bind, Except.bind, pure, Except.pure] at h
        split at h
        · exact absurd h (by simp)
        · split at h <;> exact absurd h (by simp)
      | ok r3 =>
        obtain ⟨bytes, br3⟩ := r3
        simp only [h1, h2, h3, bind, Except.bind, pure, Except.pure] at h
        split at h
        · exact absurd h (by simp)
        · split at h
          · exact absurd h (by simp)
          · simp only [Except.ok.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, _, _⟩ := h
            simp only [storedCopyLoop_size]

/-- `decodeHuffmanCurTables` preserves the buffer size (it delegates to `goCur`,
    which only writes in place). -/
theorem decodeHuffmanCurTables_size {br : ZipCommon.BitReader} {output : ByteArray} {outPos : Nat}
    {litTable distTable : HuffTree.DecodeTable} {litLD distLD : HuffTree.LongDecode} {maxOut : Nat}
    {hlp : litTable.packed.size = 2 ^ HuffTree.fastBits}
    {out : ByteArray} {p : Nat} {br' : ZipCommon.BitReader}
    (h : InflateBuf.decodeHuffmanCurTables br output outPos litTable distTable litLD distLD maxOut hlp
      = .ok (out, p, br')) :
    out.size = output.size := by
  rw [InflateBuf.decodeHuffmanCurTables] at h
  split at h
  split at h
  · simp only [bind, Except.bind] at h
    obtain ⟨pg, hg, h⟩ := bindOk' h
    obtain ⟨og, oo, opp, obb, occ⟩ := pg
    simp only [Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, _, _⟩ := h
    exact goCur_size _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hg
  · exact absurd h (by simp)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
/-- **The cursor block loop never moves the cursor backward** (`outPos ≤ final op`),
    with the cursor kept in the output budget block-by-block. Lets the reverse loop
    bound every intermediate cursor by the final one. -/
theorem inflateLoopCur_outPos_mono (maxOut dataSize : Nat) (hdd : dataSize < USize.size)
    (hmo : maxOut < USize.size) :
    ∀ (br : ZipCommon.BitReader) (buf : ByteArray) (outPos : Nat),
    br.bitPos ≤ br.data.size * 8 → br.data.size = dataSize → outPos ≤ maxOut →
    ∀ (cf : ByteArray) (op ep : Nat),
    InflateBuf.inflateLoopCur br buf outPos maxOut dataSize = .ok (cf, op, ep) → outPos ≤ op := by
  intro br buf outPos
  induction br, buf, outPos using InflateBuf.inflateLoopCur.induct (dataSize := dataSize) with
  | case1 br buf outPos ih =>
    intro hbp hds hinv cf op ep h
    rw [InflateBuf.inflateLoopCur] at h
    obtain ⟨p1, hrb1, h⟩ := bindOk' h; obtain ⟨bfinal, br₁⟩ := p1; simp only [] at h
    obtain ⟨p2, hrb2, h⟩ := bindOk' h; obtain ⟨btype, br₂⟩ := p2; simp only [] at h
    have hple : br.pos ≤ br.data.size := by
      have := hbp; simp only [ZipCommon.BitReader.bitPos] at this; omega
    have hpos : br.bitOff = 0 ∨ br.pos < br.data.size := by
      have := hbp; simp only [ZipCommon.BitReader.bitPos] at this
      rcases Nat.lt_or_ge br.pos br.data.size with h' | h'
      · exact Or.inr h'
      · exact Or.inl (by omega)
    obtain ⟨_, hp₁, hl₁⟩ := ZipCommon.readBits_inv br br₁ 1 bfinal hrb1 hpos hple
    obtain ⟨hd₂, hp₂, hl₂⟩ := ZipCommon.readBits_inv br₁ br₂ 2 btype hrb2 hp₁ hl₁
    have hdata₂ : br₂.data.size = dataSize := by
      rw [ZipCommon.readBits_data_eq br₁ br₂ 2 btype hrb2,
        ZipCommon.readBits_data_eq br br₁ 1 bfinal hrb1]; exact hds
    have hdsz₂ : br₂.data.size < USize.size := by rw [hdata₂]; exact hdd
    have houtsz : outPos < USize.size := Nat.lt_of_le_of_lt hinv hmo
    have hbtv : btype = 0 ∨ btype = 1 ∨ btype = 2 ∨ btype = 3 := by
      have hb4 : btype.toNat < 4 := Inflate.readBits_lt (n := 2) (by omega) hrb2
      rcases (show btype.toNat = 0 ∨ btype.toNat = 1 ∨ btype.toNat = 2 ∨ btype.toNat = 3 from by omega)
        with h' | h' | h' | h'
      · exact Or.inl (UInt32.toNat_inj.mp (by rw [h']; rfl))
      · exact Or.inr (Or.inl (UInt32.toNat_inj.mp (by rw [h']; rfl)))
      · exact Or.inr (Or.inr (Or.inl (UInt32.toNat_inj.mp (by rw [h']; rfl))))
      · exact Or.inr (Or.inr (Or.inr (UInt32.toNat_inj.mp (by rw [h']; rfl))))
    have htail : ∀ (co : ByteArray) (cop : Nat) (cbr : ZipCommon.BitReader),
        outPos ≤ cop → cop ≤ maxOut → cbr.data.size = dataSize →
        (if bfinal == 1 then pure (co, cop, cbr.alignToByte.pos)
         else if _h : cbr.bitPos ≤ br.bitPos then throw "Inflate: no progress in inflate loop"
              else if _h : dataSize * 8 < cbr.bitPos then throw "Inflate: bit position out of range"
              else InflateBuf.inflateLoopCur cbr co cop maxOut dataSize) = .ok (cf, op, ep) → outPos ≤ op := by
      intro co cop cbr hle hcopmax hcbrdata htc
      by_cases hbf : (bfinal == 1) = true
      · rw [if_pos hbf] at htc; simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at htc
        obtain ⟨_, rfl, _⟩ := htc; exact hle
      · rw [if_neg hbf] at htc
        by_cases hg1 : cbr.bitPos ≤ br.bitPos
        · rw [dif_pos hg1] at htc; exact absurd htc (by simp)
        · rw [dif_neg hg1] at htc
          by_cases hg2 : dataSize * 8 < cbr.bitPos
          · rw [dif_pos hg2] at htc; exact absurd htc (by simp)
          · rw [dif_neg hg2] at htc
            exact Nat.le_trans hle
              (ih co cop cbr hg1 hg2 (by rw [hcbrdata]; omega) hcbrdata hcopmax cf op ep htc)
    simp only [hrb1, hrb2, bind, Except.bind] at h
    rcases hbtv with rfl | rfl | rfl | rfl
    · obtain ⟨pb, hblock, htl⟩ := bindOk' h; obtain ⟨co, cop, cbr⟩ := pb; simp only [] at htl
      exact htail co cop cbr (decodeStoredCur_outPos_mono hblock)
        (decodeStoredCur_outPos_le_maxOut hblock)
        (by rw [decodeStoredCur_data hblock]; exact hdata₂) htl
    · obtain ⟨pb, hblock, htl⟩ := bindOk' h; obtain ⟨co, cop, cbr⟩ := pb; simp only [] at htl
      exact htail co cop cbr (decodeHuffmanCurTables_outPos_mono hdsz₂ hmo houtsz hblock)
        (decodeHuffmanCurTables_outPos_le_maxOut hdsz₂ hmo houtsz hinv hblock)
        (by rw [decodeHuffmanCurTables_data hdsz₂ hblock]; exact hdata₂) htl
    · obtain ⟨pdt, hdt, h⟩ := bindOk' h; obtain ⟨litLens, distLens, br₃⟩ := pdt; try simp only [] at h
      obtain ⟨pb, hblock, htl⟩ := bindOk' h; obtain ⟨co, cop, cbr⟩ := pb; simp only [] at htl
      obtain ⟨hdyntrees, _, _, _, _⟩ := Inflate.decodeDynamicTrees_of_lengthsOnly hdt
      obtain ⟨hd₃, hp₃, hl₃⟩ := Zip.Native.decodeDynamicTrees_inv br₂ br₃ _ _ hdyntrees hp₂ hl₂
      have hdata₃ : br₃.data.size = dataSize := by rw [hd₃]; exact hdata₂
      have hdsz₃ : br₃.data.size < USize.size := by rw [hdata₃]; exact hdd
      exact htail co cop cbr (decodeHuffmanCurTables_outPos_mono hdsz₃ hmo houtsz hblock)
        (decodeHuffmanCurTables_outPos_le_maxOut hdsz₃ hmo houtsz hinv hblock)
        (by rw [decodeHuffmanCurTables_data hdsz₃ hblock]; exact hdata₃) htl
    · exact absurd h (by simp [bind, Except.bind])

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
/-- **The block-loop bisimulation.** The cursor block loop `inflateLoopCur`
    re-represents the reference `inflateLoopTreeFree` (which is `Inflate.inflate`,
    `inflateRaw_eq_loop`): identical `btype` dispatch and `BitReader` bookkeeping,
    each block bridged by `decodeStoredCur_eq` / `decodeHuffmanCurTables_eq`,
    threading the cursor invariant `refOutput = buf.extract 0 outPos` with room
    from `inflateLoopTreeFree_size_mono`. -/
theorem inflateLoopCur_eq (maxOut dataSize : Nat) (hdd : dataSize < USize.size) :
    ∀ (br : ZipCommon.BitReader) (buf : ByteArray) (outPos : Nat) (rf : ByteArray) (endPos : Nat),
    br.bitPos ≤ br.data.size * 8 → br.data.size = dataSize → buf.size < USize.size →
    outPos ≤ buf.size → rf.size ≤ buf.size →
    Inflate.inflateLoopTreeFree br (buf.extract 0 outPos) maxOut dataSize = .ok (rf, endPos) →
    ∃ cf, InflateBuf.inflateLoopCur br buf outPos maxOut dataSize = .ok (cf, rf.size, endPos)
      ∧ cf.extract 0 rf.size = rf ∧ cf.size = buf.size := by
  intro br buf outPos
  induction br, buf, outPos using InflateBuf.inflateLoopCur.induct (dataSize := dataSize) with
  | case1 br buf outPos ih =>
    intro rf endPos hbp hds hbuf hout hroom href
    have hos : (buf.extract 0 outPos).size = outPos := by rw [ByteArray.size_extract]; omega
    rw [Inflate.inflateLoopTreeFree] at href
    obtain ⟨p1, hrb1, href⟩ := bindOk' href; obtain ⟨bfinal, br₁⟩ := p1; simp only [] at href
    obtain ⟨p2, hrb2, href⟩ := bindOk' href; obtain ⟨btype, br₂⟩ := p2; simp only [] at href
    have hbo₂ : br₂.bitOff < 8 := InflateBuf.readBits_bitOff_lt_pos (by omega) hrb2
    have hple : br.pos ≤ br.data.size := by
      have := hbp; simp only [ZipCommon.BitReader.bitPos] at this; omega
    have hpos : br.bitOff = 0 ∨ br.pos < br.data.size := by
      have := hbp; simp only [ZipCommon.BitReader.bitPos] at this
      rcases Nat.lt_or_ge br.pos br.data.size with h | h
      · exact Or.inr h
      · exact Or.inl (by omega)
    obtain ⟨_, hp₁, hl₁⟩ := ZipCommon.readBits_inv br br₁ 1 bfinal hrb1 hpos hple
    obtain ⟨hd₂, hp₂, hl₂⟩ := ZipCommon.readBits_inv br₁ br₂ 2 btype hrb2 hp₁ hl₁
    have hdata₂ : br₂.data.size = dataSize := by
      rw [ZipCommon.readBits_data_eq br₁ br₂ 2 btype hrb2,
        ZipCommon.readBits_data_eq br br₁ 1 bfinal hrb1]; exact hds
    have hbp₂ : br₂.bitPos ≤ br₂.data.size * 8 := by
      simp only [ZipCommon.BitReader.bitPos]; rcases hp₂ with h' | h' <;> omega
    -- The reference block output is a prefix of the final `rf` (via loop mono).
    have refmono : ∀ (o' : ByteArray) (b' : ZipCommon.BitReader), b'.data.size = dataSize →
        (if bfinal == 1 then pure (o', b'.alignToByte.pos)
         else if _h : b'.bitPos ≤ br.bitPos then throw "Inflate: no progress in inflate loop"
              else if _h : dataSize * 8 < b'.bitPos then throw "Inflate: bit position out of range"
              else Inflate.inflateLoopTreeFree b' o' maxOut dataSize) = .ok (rf, endPos) →
        o'.size ≤ rf.size := by
      intro o' b' hds' ht
      by_cases hbf : (bfinal == 1) = true
      · rw [if_pos hbf] at ht; simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at ht
        exact Nat.le_of_eq (congrArg ByteArray.size ht.1)
      · rw [if_neg hbf] at ht
        by_cases hg1 : b'.bitPos ≤ br.bitPos
        · rw [dif_pos hg1] at ht; exact absurd ht (by simp)
        · rw [dif_neg hg1] at ht
          by_cases hg2 : dataSize * 8 < b'.bitPos
          · rw [dif_pos hg2] at ht; exact absurd ht (by simp)
          · rw [dif_neg hg2] at ht
            exact inflateLoopTreeFree_size_mono maxOut dataSize hdd b' o' rf endPos
              (by rw [hds']; omega) hds' ht
    -- The shared tail: from the block's cursor result, finish or recurse.
    have htailcur : ∀ (refOut' cf' : ByteArray) (br' : ZipCommon.BitReader),
        cf'.extract 0 refOut'.size = refOut' → cf'.size = buf.size → br'.data.size = dataSize →
        (if bfinal == 1 then pure (refOut', br'.alignToByte.pos)
         else if _h : br'.bitPos ≤ br.bitPos then throw "Inflate: no progress in inflate loop"
              else if _h : dataSize * 8 < br'.bitPos then throw "Inflate: bit position out of range"
              else Inflate.inflateLoopTreeFree br' refOut' maxOut dataSize) = .ok (rf, endPos) →
        ∃ cf, (if bfinal == 1 then pure (cf', refOut'.size, br'.alignToByte.pos)
               else if _h : br'.bitPos ≤ br.bitPos then throw "Inflate: no progress in inflate loop"
                    else if _h : dataSize * 8 < br'.bitPos then throw "Inflate: bit position out of range"
                    else InflateBuf.inflateLoopCur br' cf' refOut'.size maxOut dataSize)
                = .ok (cf, rf.size, endPos) ∧ cf.extract 0 rf.size = rf ∧ cf.size = buf.size := by
      intro refOut' cf' br' hext hcsize hds' ht
      have hmono := refmono refOut' br' hds' ht
      by_cases hbf : (bfinal == 1) = true
      · rw [if_pos hbf] at ht ⊢
        simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at ht
        obtain ⟨hrfeq, hendeq⟩ := ht
        exact ⟨cf', by simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq, hrfeq, hendeq],
          by rw [← hrfeq]; exact hext, hcsize⟩
      · rw [if_neg hbf] at ht ⊢
        by_cases hg1 : br'.bitPos ≤ br.bitPos
        · rw [dif_pos hg1] at ht; exact absurd ht (by simp)
        · rw [dif_neg hg1] at ht ⊢
          by_cases hg2 : dataSize * 8 < br'.bitPos
          · rw [dif_pos hg2] at ht; exact absurd ht (by simp)
          · rw [dif_neg hg2] at ht ⊢
            rw [← hext] at ht
            obtain ⟨cf'', h1, h2, h3⟩ := ih cf' refOut'.size br' hg1 hg2 rf endPos
              (by rw [hds']; omega) hds' (by rw [hcsize]; exact hbuf)
              (by rw [hcsize]; exact Nat.le_trans hmono hroom) (by rw [hcsize]; exact hroom) ht
            exact ⟨cf'', h1, h2, by rw [h3]; exact hcsize⟩
    have hbtv : btype = 0 ∨ btype = 1 ∨ btype = 2 ∨ btype = 3 := by
      have hb4 : btype.toNat < 4 := Inflate.readBits_lt (n := 2) (by omega) hrb2
      rcases (show btype.toNat = 0 ∨ btype.toNat = 1 ∨ btype.toNat = 2 ∨ btype.toNat = 3 from by omega)
        with h' | h' | h' | h'
      · exact Or.inl (UInt32.toNat_inj.mp (by rw [h']; rfl))
      · exact Or.inr (Or.inl (UInt32.toNat_inj.mp (by rw [h']; rfl)))
      · exact Or.inr (Or.inr (Or.inl (UInt32.toNat_inj.mp (by rw [h']; rfl))))
      · exact Or.inr (Or.inr (Or.inr (UInt32.toNat_inj.mp (by rw [h']; rfl))))
    rw [InflateBuf.inflateLoopCur]
    simp only [hrb1, hrb2, bind, Except.bind]
    simp only [bind, Except.bind] at href
    rcases hbtv with rfl | rfl | rfl | rfl
    · -- stored
      obtain ⟨pb, hblock, htl⟩ := bindOk' href; obtain ⟨refOut', br'⟩ := pb; simp only [] at htl
      have hbroom : refOut'.size ≤ buf.size :=
        Nat.le_trans (refmono refOut' br' (by
          obtain ⟨hd', _, _⟩ := Zip.Native.decodeStored_inv br₂ br' _ refOut' maxOut hblock
          rw [hd']; exact hdata₂) htl) hroom
      obtain ⟨hd', _, _⟩ := Zip.Native.decodeStored_inv br₂ br' _ refOut' maxOut hblock
      obtain ⟨cf', hcur, hext', hcsize'⟩ :=
        decodeStoredCur_eq br₂ buf outPos maxOut hout refOut' br' hblock hbroom
      rw [hcur]; simp only [bind, Except.bind]
      exact htailcur refOut' cf' br' hext' hcsize' (by rw [hd']; exact hdata₂) htl
    · -- fixed Huffman
      obtain ⟨pb, hblock, htl⟩ := bindOk' href; obtain ⟨refOut', br'⟩ := pb; simp only [] at htl
      rw [Inflate.decodeHuffmanFastBufFixed] at hblock
      have hbr := decodeHuffmanFastBufTables_br br₂ _ _ _ _ _ maxOut _
        (by rw [hdata₂]; exact hdd) refOut' br' hblock
      have hbroom : refOut'.size ≤ buf.size :=
        Nat.le_trans (refmono refOut' br' (by rw [hbr.1]; exact hdata₂) htl) hroom
      obtain ⟨cf', hcur, hext', hcsize'⟩ :=
        decodeHuffmanCurTables_eq br₂ buf outPos _ _ _ _ maxOut _
          (by rw [hdata₂]; exact hdd) hbo₂ hbp₂ hout hbuf refOut' br' hblock hbroom
      rw [hcur]; simp only [bind, Except.bind]
      exact htailcur refOut' cf' br' hext' hcsize' (by rw [hbr.1]; exact hdata₂) htl
    · -- dynamic Huffman
      obtain ⟨pdt, hdt, href⟩ := bindOk' href; obtain ⟨litLens, distLens, br₃⟩ := pdt; try simp only [] at href
      obtain ⟨pb, hblock, htl⟩ := bindOk' href; obtain ⟨refOut', br'⟩ := pb; simp only [] at htl
      obtain ⟨hdyntrees, _, _, _, _⟩ := Inflate.decodeDynamicTrees_of_lengthsOnly hdt
      obtain ⟨hd₃, hp₃, hl₃⟩ := Zip.Native.decodeDynamicTrees_inv br₂ br₃ _ _ hdyntrees hp₂ hl₂
      have hbo₃ := InflateBuf.decodeDynamicTrees_bitOff_pres hbo₂ hdyntrees
      have hdata₃ : br₃.data.size = dataSize := by rw [hd₃]; exact hdata₂
      have hbp₃ : br₃.bitPos ≤ br₃.data.size * 8 := by
        simp only [ZipCommon.BitReader.bitPos]; rcases hp₃ with h' | h' <;> omega
      rw [InflateBuf.decodeHuffmanFastBufTreeFree] at hblock
      have hbr := decodeHuffmanFastBufTables_br br₃ _ _ _ _ _ maxOut _
        (by rw [hdata₃]; exact hdd) refOut' br' hblock
      have hbroom : refOut'.size ≤ buf.size :=
        Nat.le_trans (refmono refOut' br' (by rw [hbr.1]; exact hdata₃) htl) hroom
      obtain ⟨cf', hcur, hext', hcsize'⟩ :=
        decodeHuffmanCurTables_eq br₃ buf outPos _ _ _ _ maxOut _
          (by rw [hdata₃]; exact hdd) hbo₃ hbp₃ hout hbuf refOut' br' hblock hbroom
      simp only [hdt, bind, Except.bind]
      rw [hcur]; simp only [bind, Except.bind]
      exact htailcur refOut' cf' br' hext' hcsize' (by rw [hbr.1]; exact hdata₃) htl
    · -- reserved
      exact absurd href (by simp [bind, Except.bind])

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
/-- **Reverse of `inflateLoopCur_eq`**: whenever the cursor block loop succeeds (its
    final cursor fitting the buffer — the exact-size regime), the reference loop on
    the logical prefix succeeds with the same tail bytes. With `inflateLoopCur_eq`
    and determinism this pins `inflateLoopCur`-accepts ⟺ `inflateLoopTreeFree`-accepts.
    Same one-case `inflateLoopCur.induct`; each block goes through the reverse block
    bridge, `inflateLoopCur_outPos_mono` bounds every block cursor by the final `op`. -/
theorem inflateLoopCur_treeFree (maxOut dataSize : Nat) (hdd : dataSize < USize.size)
    (hmo : maxOut < USize.size) :
    ∀ (br : ZipCommon.BitReader) (buf : ByteArray) (outPos : Nat) (cf : ByteArray) (op ep : Nat),
    br.bitPos ≤ br.data.size * 8 → br.data.size = dataSize → buf.size < USize.size →
    buf.size ≤ maxOut → outPos ≤ buf.size →
    InflateBuf.inflateLoopCur br buf outPos maxOut dataSize = .ok (cf, op, ep) → op ≤ buf.size →
    Inflate.inflateLoopTreeFree br (buf.extract 0 outPos) maxOut dataSize
      = .ok (cf.extract 0 op, ep) := by
  intro br buf outPos
  induction br, buf, outPos using InflateBuf.inflateLoopCur.induct (dataSize := dataSize) with
  | case1 br buf outPos ih =>
    intro cf op ep hbp hds hbuf hbm hout h hop
    rw [InflateBuf.inflateLoopCur] at h
    obtain ⟨p1, hrb1, h⟩ := bindOk' h; obtain ⟨bfinal, br₁⟩ := p1; simp only [] at h
    obtain ⟨p2, hrb2, h⟩ := bindOk' h; obtain ⟨btype, br₂⟩ := p2; simp only [] at h
    have hbo₂ : br₂.bitOff < 8 := InflateBuf.readBits_bitOff_lt_pos (by omega) hrb2
    have hple : br.pos ≤ br.data.size := by
      have := hbp; simp only [ZipCommon.BitReader.bitPos] at this; omega
    have hpos : br.bitOff = 0 ∨ br.pos < br.data.size := by
      have := hbp; simp only [ZipCommon.BitReader.bitPos] at this
      rcases Nat.lt_or_ge br.pos br.data.size with h' | h'
      · exact Or.inr h'
      · exact Or.inl (by omega)
    obtain ⟨_, hp₁, hl₁⟩ := ZipCommon.readBits_inv br br₁ 1 bfinal hrb1 hpos hple
    obtain ⟨hd₂, hp₂, hl₂⟩ := ZipCommon.readBits_inv br₁ br₂ 2 btype hrb2 hp₁ hl₁
    have hdata₂ : br₂.data.size = dataSize := by
      rw [ZipCommon.readBits_data_eq br₁ br₂ 2 btype hrb2,
        ZipCommon.readBits_data_eq br br₁ 1 bfinal hrb1]; exact hds
    have hbp₂ : br₂.bitPos ≤ br₂.data.size * 8 := by
      simp only [ZipCommon.BitReader.bitPos]; rcases hp₂ with h' | h' <;> omega
    have htail : ∀ (co : ByteArray) (cop : Nat) (cbr : ZipCommon.BitReader),
        co.size = buf.size → cbr.data.size = dataSize → cop ≤ maxOut →
        (if bfinal == 1 then pure (co, cop, cbr.alignToByte.pos)
         else if _h : cbr.bitPos ≤ br.bitPos then throw "Inflate: no progress in inflate loop"
              else if _h : dataSize * 8 < cbr.bitPos then throw "Inflate: bit position out of range"
              else InflateBuf.inflateLoopCur cbr co cop maxOut dataSize) = .ok (cf, op, ep) →
        cop ≤ op ∧ (if bfinal == 1 then pure (co.extract 0 cop, cbr.alignToByte.pos)
                    else if _h : cbr.bitPos ≤ br.bitPos then throw "Inflate: no progress in inflate loop"
                         else if _h : dataSize * 8 < cbr.bitPos then throw "Inflate: bit position out of range"
                         else Inflate.inflateLoopTreeFree cbr (co.extract 0 cop) maxOut dataSize)
                    = .ok (cf.extract 0 op, ep) := by
      intro co cop cbr hcosz hcbrdata hcopmax htc
      by_cases hbf : (bfinal == 1) = true
      · rw [if_pos hbf] at htc ⊢
        simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at htc
        obtain ⟨rfl, rfl, rfl⟩ := htc
        exact ⟨Nat.le_refl _, by simp only [pure, Except.pure]⟩
      · rw [if_neg hbf] at htc ⊢
        by_cases hg1 : cbr.bitPos ≤ br.bitPos
        · rw [dif_pos hg1] at htc; exact absurd htc (by simp)
        · rw [dif_neg hg1] at htc ⊢
          by_cases hg2 : dataSize * 8 < cbr.bitPos
          · rw [dif_pos hg2] at htc; exact absurd htc (by simp)
          · rw [dif_neg hg2] at htc ⊢
            have hcople := inflateLoopCur_outPos_mono maxOut dataSize hdd hmo cbr co cop
              (by rw [hcbrdata]; omega) hcbrdata hcopmax cf op ep htc
            exact ⟨hcople, ih co cop cbr hg1 hg2 cf op ep (by rw [hcbrdata]; omega) hcbrdata
              (by rw [hcosz]; exact hbuf) (by rw [hcosz]; exact hbm)
              (by rw [hcosz]; exact Nat.le_trans hcople hop) htc (by rw [hcosz]; exact hop)⟩
    rw [Inflate.inflateLoopTreeFree]
    simp only [hrb1, hrb2, bind, Except.bind]
    simp only [hrb1, hrb2, bind, Except.bind] at h
    rcases hbtv : (show btype = 0 ∨ btype = 1 ∨ btype = 2 ∨ btype = 3 from by
      have hb4 : btype.toNat < 4 := Inflate.readBits_lt (n := 2) (by omega) hrb2
      rcases (show btype.toNat = 0 ∨ btype.toNat = 1 ∨ btype.toNat = 2 ∨ btype.toNat = 3 from by omega)
        with h' | h' | h' | h'
      · exact Or.inl (UInt32.toNat_inj.mp (by rw [h']; rfl))
      · exact Or.inr (Or.inl (UInt32.toNat_inj.mp (by rw [h']; rfl)))
      · exact Or.inr (Or.inr (Or.inl (UInt32.toNat_inj.mp (by rw [h']; rfl))))
      · exact Or.inr (Or.inr (Or.inr (UInt32.toNat_inj.mp (by rw [h']; rfl))))) with rfl | rfl | rfl | rfl
    · obtain ⟨pb, hblock, htl⟩ := bindOk' h; obtain ⟨co, cop, cbr⟩ := pb; simp only [] at htl
      obtain ⟨hcople, hreftail⟩ := htail co cop cbr (decodeStoredCur_size hblock)
        (by rw [decodeStoredCur_data hblock]; exact hdata₂)
        (decodeStoredCur_outPos_le_maxOut hblock) htl
      rw [decodeStoredCur_treeFree br₂ buf outPos maxOut hout co cop cbr hblock
        (Nat.le_trans hcople hop)]
      simp only [bind, Except.bind]; exact hreftail
    · obtain ⟨pb, hblock, htl⟩ := bindOk' h; obtain ⟨co, cop, cbr⟩ := pb; simp only [] at htl
      obtain ⟨hcople, hreftail⟩ := htail co cop cbr (decodeHuffmanCurTables_size hblock)
        (by rw [decodeHuffmanCurTables_data (by rw [hdata₂]; exact hdd) hblock]; exact hdata₂)
        (decodeHuffmanCurTables_outPos_le_maxOut (by rw [hdata₂]; exact hdd) hmo
          (Nat.lt_of_le_of_lt hout hbuf) (Nat.le_trans hout hbm) hblock) htl
      rw [Inflate.decodeHuffmanFastBufFixed,
        decodeHuffmanCurTables_treeFree br₂ buf outPos _ _ _ _ maxOut _
          (by rw [hdata₂]; exact hdd) hbo₂ hbp₂ hout hbuf hmo co cop cbr hblock
          (Nat.le_trans hcople hop)]
      simp only [bind, Except.bind]; exact hreftail
    · obtain ⟨pdt, hdt, h⟩ := bindOk' h; obtain ⟨litLens, distLens, br₃⟩ := pdt; try simp only [] at h
      obtain ⟨pb, hblock, htl⟩ := bindOk' h; obtain ⟨co, cop, cbr⟩ := pb; simp only [] at htl
      obtain ⟨hdyntrees, _, _, _, _⟩ := Inflate.decodeDynamicTrees_of_lengthsOnly hdt
      obtain ⟨hd₃, hp₃, hl₃⟩ := Zip.Native.decodeDynamicTrees_inv br₂ br₃ _ _ hdyntrees hp₂ hl₂
      have hbo₃ := InflateBuf.decodeDynamicTrees_bitOff_pres hbo₂ hdyntrees
      have hdata₃ : br₃.data.size = dataSize := by rw [hd₃]; exact hdata₂
      have hbp₃ : br₃.bitPos ≤ br₃.data.size * 8 := by
        simp only [ZipCommon.BitReader.bitPos]; rcases hp₃ with h' | h' <;> omega
      obtain ⟨hcople, hreftail⟩ := htail co cop cbr (decodeHuffmanCurTables_size hblock)
        (by rw [decodeHuffmanCurTables_data (by rw [hdata₃]; exact hdd) hblock]; exact hdata₃)
        (decodeHuffmanCurTables_outPos_le_maxOut (by rw [hdata₃]; exact hdd) hmo
          (Nat.lt_of_le_of_lt hout hbuf) (Nat.le_trans hout hbm) hblock) htl
      simp only [hdt, bind, Except.bind]
      rw [InflateBuf.decodeHuffmanFastBufTreeFree,
        decodeHuffmanCurTables_treeFree br₃ buf outPos _ _ _ _ maxOut _
          (by rw [hdata₃]; exact hdd) hbo₃ hbp₃ hout hbuf hmo co cop cbr hblock
          (Nat.le_trans hcople hop)]
      simp only [bind, Except.bind]; exact hreftail
    · exact absurd h (by simp [bind, Except.bind])

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
/-- **The cursor block loop preserves the buffer size** (every block writes in
    place). Needed so the exact-size contract pins the cursor to `sizeHint`. -/
theorem inflateLoopCur_size (maxOut dataSize : Nat) :
    ∀ (br : ZipCommon.BitReader) (buf : ByteArray) (outPos : Nat) (cf : ByteArray) (op ep : Nat),
    InflateBuf.inflateLoopCur br buf outPos maxOut dataSize = .ok (cf, op, ep) → cf.size = buf.size := by
  intro br buf outPos
  induction br, buf, outPos using InflateBuf.inflateLoopCur.induct (dataSize := dataSize) with
  | case1 br buf outPos ih =>
    intro cf op ep h
    rw [InflateBuf.inflateLoopCur] at h
    obtain ⟨p1, hrb1, h⟩ := bindOk' h; obtain ⟨bfinal, br₁⟩ := p1; simp only [] at h
    obtain ⟨p2, hrb2, h⟩ := bindOk' h; obtain ⟨btype, br₂⟩ := p2; simp only [] at h
    have hbtv : btype = 0 ∨ btype = 1 ∨ btype = 2 ∨ btype = 3 := by
      have hb4 : btype.toNat < 4 := Inflate.readBits_lt (n := 2) (by omega) hrb2
      rcases (show btype.toNat = 0 ∨ btype.toNat = 1 ∨ btype.toNat = 2 ∨ btype.toNat = 3 from by omega)
        with h' | h' | h' | h'
      · exact Or.inl (UInt32.toNat_inj.mp (by rw [h']; rfl))
      · exact Or.inr (Or.inl (UInt32.toNat_inj.mp (by rw [h']; rfl)))
      · exact Or.inr (Or.inr (Or.inl (UInt32.toNat_inj.mp (by rw [h']; rfl))))
      · exact Or.inr (Or.inr (Or.inr (UInt32.toNat_inj.mp (by rw [h']; rfl))))
    have htail : ∀ (co : ByteArray) (cop : Nat) (cbr : ZipCommon.BitReader), co.size = buf.size →
        (if bfinal == 1 then pure (co, cop, cbr.alignToByte.pos)
         else if _h : cbr.bitPos ≤ br.bitPos then throw "Inflate: no progress in inflate loop"
              else if _h : dataSize * 8 < cbr.bitPos then throw "Inflate: bit position out of range"
              else InflateBuf.inflateLoopCur cbr co cop maxOut dataSize) = .ok (cf, op, ep) →
        cf.size = buf.size := by
      intro co cop cbr hcosz htc
      by_cases hbf : (bfinal == 1) = true
      · rw [if_pos hbf] at htc; simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at htc
        obtain ⟨rfl, _, _⟩ := htc; exact hcosz
      · rw [if_neg hbf] at htc
        by_cases hg1 : cbr.bitPos ≤ br.bitPos
        · rw [dif_pos hg1] at htc; exact absurd htc (by simp)
        · rw [dif_neg hg1] at htc
          by_cases hg2 : dataSize * 8 < cbr.bitPos
          · rw [dif_pos hg2] at htc; exact absurd htc (by simp)
          · rw [dif_neg hg2] at htc
            rw [ih co cop cbr hg1 hg2 cf op ep htc]; exact hcosz
    simp only [hrb1, hrb2, bind, Except.bind] at h
    rcases hbtv with rfl | rfl | rfl | rfl
    · obtain ⟨pb, hblock, htl⟩ := bindOk' h; obtain ⟨co, cop, cbr⟩ := pb; simp only [] at htl
      exact htail co cop cbr (decodeStoredCur_size hblock) htl
    · obtain ⟨pb, hblock, htl⟩ := bindOk' h; obtain ⟨co, cop, cbr⟩ := pb; simp only [] at htl
      exact htail co cop cbr (decodeHuffmanCurTables_size hblock) htl
    · obtain ⟨pdt, hdt, h⟩ := bindOk' h; obtain ⟨litLens, distLens, br₃⟩ := pdt; try simp only [] at h
      obtain ⟨pb, hblock, htl⟩ := bindOk' h; obtain ⟨co, cop, cbr⟩ := pb; simp only [] at htl
      exact htail co cop cbr (decodeHuffmanCurTables_size hblock) htl
    · exact absurd h (by simp [bind, Except.bind])

set_option maxHeartbeats 1000000 in
/-- **Target (issue #2799): the write-once cursor decoder agrees with the verified
    decoder on the exact-size path.** Whenever the verified tree-free decoder
    `Inflate.inflate` produces `out`, the write-once cursor decoder run with the
    exact size hint `out.size` produces the same bytes. The hypotheses
    `data.size < USize.size` / `out.size < USize.size` are addressability (always
    true for in-memory `ByteArray`s — the wide-buffer branch the cursor takes),
    and `out.size ≤ maxOut` holds for any output the bounded reference produced.

    Chains `Inflate.inflate = inflateLoopTreeFree` (`inflateRaw_eq_loop`), the loop
    bisimulation `inflateLoopCur_eq` on the presized buffer, then the exact-size
    contract (`cf.size = out.size`, so `cf = out`). -/
theorem inflateFast_eq (data : ByteArray) (maxOut : Nat) (out : ByteArray)
    (hds : data.size < USize.size) (hosz : out.size < USize.size) (hle : out.size ≤ maxOut)
    (href : Inflate.inflate data maxOut = .ok out) :
    Inflate.inflateFast data maxOut out.size = .ok out := by
  have hpsz : (ByteArray.presize out.size).size = out.size := by
    simp only [ByteArray.presize, ByteArray.size, Array.size_replicate]
  -- Reference `inflate` → tree-free block loop over the empty output.
  rw [Inflate.inflate] at href
  obtain ⟨pr, hraw, hret⟩ := bindOk' href
  obtain ⟨out', endPos⟩ := pr
  simp only [pure, Except.pure, Except.ok.injEq] at hret; rw [hret] at hraw
  rw [Inflate.inflateRaw_eq_loop] at hraw
  have hemp : ByteArray.emptyWithCapacity 0 = (ByteArray.presize out.size).extract 0 0 := by
    apply ByteArray.ext_getElem!
    · rw [ByteArray.size_extract]; simp
    · intro i hi; simp at hi
  rw [hemp] at hraw
  -- Loop bisimulation on the presized buffer.
  obtain ⟨cf, hcur, hext, hcsize⟩ := inflateLoopCur_eq maxOut data.size hds
    { data := data, pos := 0, bitOff := 0 } (ByteArray.presize out.size) 0 out endPos
    (by simp [ZipCommon.BitReader.bitPos]) rfl (by rw [hpsz]; exact hosz) (by omega)
    (Nat.le_of_eq hpsz.symm) hraw
  have hcfsz : cf.size = out.size := by rw [hcsize, hpsz]
  have hcfout : cf = out := by
    apply ByteArray.ext_getElem! hcfsz
    intro i hi
    rw [← hext, ByteArray.getElem!_extract _ 0 _ i (by rw [hcfsz] at hi; omega), Nat.zero_add]
  -- `inflateFast` runs the same loop and passes the exact-size check.
  rw [Inflate.inflateFast, Inflate.inflateRawFast]
  simp only [bind, Except.bind]
  rw [if_neg (by omega : ¬ out.size > maxOut)]
  simp only [bind, Except.bind, hcur]
  rw [if_neg (by rw [hcfsz]; simp)]
  simp only [pure, Except.pure, hcfout]

/-! ### The `uset` margin-split fastloop (`goCurU`) equals the `set!` cursor (`goCur`)

`goCurU` is `goCur` with the per-symbol capacity checks hoisted to a single
`outPos + 299 ≤ output.size` margin guard, `uset` in place of `set!`, and a
`length ≤ 258` check in the match (the copy overshoots into the margin). Under
`output.size ≤ maxOut` the two are result-identical: the margin discharges every
per-symbol `maxOut` check `goCur` makes, `uset = set!` in bounds, and DEFLATE
`length ≤ 258` kills the extra check. The `< 299`-byte tail literally *is* `goCur`. -/

/-- `uset` (proven-bounds) is `set!` in bounds. -/
theorem ByteArray.uset_eq_set! (a : ByteArray) (i : USize) (v : UInt8) (h : i.toNat < a.size) :
    a.uset i v h = a.set! i.toNat v := by
  have hd : i.toNat < a.data.size := h
  simp only [ByteArray.uset, ByteArray.set!, Array.uset_eq_set, Array.set!_eq_setIfInBounds]
  congr 1
  rw [Array.setIfInBounds, dif_pos hd]

/-- `takeBits` extracts a value below `2^n`. -/
theorem takeBits_lt (bitBuf : UInt64) (cnt n : Nat) (hn : n < 64) {v : Nat} {bb : UInt64} {c : Nat}
    (h : InflateBuf.takeBits bitBuf cnt n = .ok (v, bb, c)) : v < 2 ^ n := by
  unfold InflateBuf.takeBits at h
  split at h
  · exact absurd h (by simp)
  · simp only [Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, _⟩ := h; exact InflateBuf.mask_lt hn

/-- **DEFLATE lengths are ≤ 258**: `lengthBase[idx] + eb ≤ 258` for any extra-bits
    value below `2^lengthExtra[idx]`. Kills `goCurU`'s `length > 258` guard. -/
theorem length_le_258 (idx : Nat) (h : idx < Inflate.lengthBase.size) {eb : Nat}
    (heb : eb < 2 ^ (Inflate.lengthExtra[idx]'(by
      rw [Inflate.lengthExtra_size]; rw [Inflate.lengthBase_size] at h; exact h)).toNat) :
    Inflate.lengthBase[idx].toNat + eb ≤ 258 := by
  have hex : idx < Inflate.lengthExtra.size := by
    rw [Inflate.lengthExtra_size, ← Inflate.lengthBase_size]; exact h
  have hkey : ∀ k : Fin Inflate.lengthBase.size,
      Inflate.lengthBase[k.val]!.toNat + 2 ^ Inflate.lengthExtra[k.val]!.toNat ≤ 259 := by
    decide
  have hk := hkey ⟨idx, h⟩
  rw [getElem!_pos Inflate.lengthBase idx h, getElem!_pos Inflate.lengthExtra idx hex] at hk
  omega

/-- Length extra-bit counts are all `< 64` (they max out at 5); needed to invoke
    `takeBits_lt` at the DEFLATE length codes. -/
theorem lengthExtra_lt_64 (idx : Nat) (h : idx < Inflate.lengthExtra.size) :
    (Inflate.lengthExtra[idx]).toNat < 64 := by
  have hkey : ∀ k : Fin Inflate.lengthExtra.size, Inflate.lengthExtra[k.val]!.toNat < 64 := by
    decide
  have hk := hkey ⟨idx, h⟩
  rwa [getElem!_pos Inflate.lengthExtra idx h] at hk

theorem lengthExtra_le_5 (idx : Nat) (h : idx < Inflate.lengthExtra.size) :
    (Inflate.lengthExtra[idx]).toNat ≤ 5 := by
  have hkey : ∀ k : Fin Inflate.lengthExtra.size,
      Inflate.lengthExtra[k.val]!.toNat ≤ 5 := by decide
  have hk := hkey ⟨idx, h⟩
  rwa [getElem!_pos Inflate.lengthExtra idx h] at hk

theorem distExtra_lt_64 (idx : Nat) (h : idx < Inflate.distExtra.size) :
    (Inflate.distExtra[idx]).toNat < 64 := by
  have hkey : ∀ k : Fin Inflate.distExtra.size,
      Inflate.distExtra[k.val]!.toNat < 64 := by decide
  have hk := hkey ⟨idx, h⟩
  rwa [getElem!_pos Inflate.distExtra idx h] at hk

theorem decodeSym_used_le (tree : HuffTree) (table : HuffTree.DecodeTable)
    (hdep : InflateBuf.treeDepthLE tree 15)
    (hlen : ∀ b : UInt64, (table.lenAt (b &&& 0x7FF).toNat).toNat ≤ 11)
    {b : UInt64} {n : Nat} {s : UInt16} {bb : UInt64} {c used : Nat}
    (h : InflateBuf.decodeSym tree table b n = .ok (s, bb, c, used)) : used ≤ 15 := by
  simp only [InflateBuf.decodeSym] at h
  split at h
  · exact InflateBuf.walkTree_used_le tree h hdep
  · simp only [Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨_, _, _, rfl⟩ := h
    exact Nat.le_trans (hlen b) (by omega)

theorem treeFree_len_le (lengths : Array UInt8)
    (hv : Huffman.Spec.ValidLengths (lengths.toList.map UInt8.toNat) 15)
    (hbound : lengths.size ≤ UInt16.size) (b : UInt64) :
    ((HuffTree.buildTreeFreeWithCount lengths (HuffTree.countLengthsFast lengths 15) 15).1.lenAt
      (b &&& 0x7FF).toNat).toNat ≤ 11 := by
  rw [HuffTree.treeFree_lenAt_eq lengths 15 (by omega) hv hbound _ (InflateBuf.buf_idx_lt b)]
  exact InflateBuf.buildTable_codeLen_le _ _ (InflateBuf.buf_idx_lt b)

theorem treeFree_decode_used_le (lengths : Array UInt8)
    (hv : Huffman.Spec.ValidLengths (lengths.toList.map UInt8.toNat) 15)
    (hbound : lengths.size ≤ UInt16.size)
    {b : UInt64} {n : Nat} {s : UInt16} {bb : UInt64} {c used : Nat}
    (h : HuffTree.decodeSymCanon
      (HuffTree.buildTreeFreeWithCount lengths (HuffTree.countLengthsFast lengths 15) 15).2
      (HuffTree.buildTreeFreeWithCount lengths (HuffTree.countLengthsFast lengths 15) 15).1
      15 b n = .ok (s, bb, c, used)) : used ≤ 15 := by
  apply decodeSym_used_le (HuffTree.fromLengthsTree lengths 15) _
    (InflateBuf.fromLengths_depthLE (HuffTree.fromLengths_ok_of_valid lengths 15 hv))
    (treeFree_len_le lengths hv hbound)
  exact (HuffTree.decodeSymCanon_treeFree_ok_iff lengths hv hbound b n _).mp h

-- Force generation of the `goCurU` functional-induction principle.
private def goCurU_induct_force := @Zip.Native.InflateBuf.goCurU.induct

set_option maxRecDepth 8192 in
/-- **The #2799 centrepiece**: the branch-free `uset` margin-split fastloop
    `goCurU` computes exactly what the bounds-checked `set!` cursor `goCur` does,
    given the invariant `output.size ≤ maxOut`. Under the per-symbol margin
    (`outPos + 299 ≤ output.size`) `goCur`'s output-size checks can never fire,
    `uset = set!` in bounds, and DEFLATE `length ≤ 258` makes `goCurU`'s cheaper
    `length > 258` guard agree with `goCur`'s `outPos + length > maxOut`; the
    `< 299`-byte tail is a literal delegation to `goCur`. -/
theorem goCurU_eq (litTable distTable : HuffTree.DecodeTable) (litLD distLD : HuffTree.LongDecode)
    (maxBits : Nat) (data : ByteArray) (maxOut : Nat) (hsz : data.size < USize.size)
    (hlp : litTable.packed.size = 2 ^ HuffTree.fastBits) :
    ∀ (pos : USize) (bitBuf : UInt64) (cnt : USize) (output : ByteArray) (outPos : USize),
    output.size ≤ maxOut →
    InflateBuf.goCurU litTable distTable litLD distLD maxBits data maxOut pos bitBuf cnt hsz hlp
        output outPos
      = goCur litTable distTable litLD distLD maxBits data maxOut pos bitBuf cnt hsz hlp
        output outPos := by
  intro pos bitBuf cnt output outPos
  induction pos, bitBuf, cnt, output, outPos using InflateBuf.goCurU.induct
    (litTable := litTable) (litLD := litLD) (maxBits := maxBits) (data := data)
    (hsz := hsz) (hlp := hlp) with
  | case1 pos bitBuf cnt output outPos hrc ih =>
    intro hsize
    rw [InflateBuf.goCurU, dif_pos hrc, goCur, dif_pos hrc]
    exact ih hsize
  | case2 pos bitBuf cnt output outPos hrc hm ent hlit ih =>
    intro hsize
    have hlt : outPos.toNat < output.size := by omega
    have hmax : ¬ outPos.toNat ≥ maxOut := by omega
    have hI := ih (by rw [ByteArray.uset_eq_set!, ByteArray.size_set!]; exact hsize)
    rw [ByteArray.uset_eq_set!] at hI
    rw [InflateBuf.goCurU, dif_neg hrc, dif_pos hm, dif_pos hlit, ByteArray.uset_eq_set!]
    rw [goCur, dif_neg hrc, dif_pos hlit, if_neg hmax]
    exact hI
  | case3 pos bitBuf cnt output outPos hrc hm ent hlit estr hde =>
    intro hsize
    rw [InflateBuf.goCurU, dif_neg hrc, dif_pos hm, dif_neg hlit]
    rw [goCur, dif_neg hrc, dif_neg hlit]
    simp only [hde]
  | case4 pos bitBuf cnt output outPos hrc hm ent hlit cnt0 sym bb c' used hde hsym hnp =>
    intro hsize
    have hmax : ¬ outPos.toNat ≥ maxOut := by omega
    rw [InflateBuf.goCurU, dif_neg hrc, dif_pos hm, dif_neg hlit]
    simp only [hde]
    rw [if_pos hsym, dif_pos hnp]
    rw [goCur, dif_neg hrc, dif_neg hlit]
    simp only [hde]
    rw [if_pos hsym, if_neg hmax, dif_pos hnp]
  | case5 pos bitBuf cnt output outPos hrc hm ent hlit cnt0 sym bb c' used hde hsym hnp ih =>
    intro hsize
    have hlt : outPos.toNat < output.size := by omega
    have hmax : ¬ outPos.toNat ≥ maxOut := by omega
    have hI := ih (by rw [ByteArray.uset_eq_set!, ByteArray.size_set!]; exact hsize)
    rw [ByteArray.uset_eq_set!] at hI
    rw [InflateBuf.goCurU, dif_neg hrc, dif_pos hm, dif_neg hlit]
    simp only [hde]
    rw [if_pos hsym, dif_neg hnp, ByteArray.uset_eq_set!]
    rw [goCur, dif_neg hrc, dif_neg hlit]
    simp only [hde]
    rw [if_pos hsym, if_neg hmax, dif_neg hnp]
    exact hI
  | case6 pos bitBuf cnt output outPos hrc hm ent hlit sym bb c' used hde hnlt heob =>
    intro hsize
    rw [InflateBuf.goCurU, dif_neg hrc, dif_pos hm, dif_neg hlit]
    simp only [hde]
    rw [if_neg hnlt, if_pos heob]
    rw [goCur, dif_neg hrc, dif_neg hlit]
    simp only [hde]
    rw [if_neg hnlt, if_pos heob]
  | case7 pos bitBuf cnt output outPos hrc hm ent hlit sym bb c' used hde hnlt hneob idx hidx =>
    intro hsize
    have hidx' : sym.toNat - 257 ≥ Inflate.lengthBase.size := hidx
    rw [InflateBuf.goCurU, dif_neg hrc, dif_pos hm, dif_neg hlit]
    simp only [hde]
    rw [if_neg hnlt, if_neg hneob, dif_pos hidx']
    rw [goCur, dif_neg hrc, dif_neg hlit]
    simp only [hde]
    rw [if_neg hnlt, if_neg hneob, dif_pos hidx']
  | case8 pos bitBuf cnt output outPos hrc hm ent hlit cnt0 sym bb c' used hde hsym hneob idx hh base ih =>
    intro hsize
    -- Normalize functional-induction's local table lets so the dependent
    -- short-copy dispatch in `ih` matches the unfolded recursive call below.
    dsimp only [base, idx] at ih
    have hhc : ¬ sym.toNat - 257 ≥ Inflate.lengthBase.size := hh
    have hhc29 : sym.toNat - 257 < 29 := by
      have := hhc; rw [Inflate.lengthBase_size] at this; omega
    rw [InflateBuf.goCurU, dif_neg hrc, dif_pos hm, dif_neg hlit]
    simp only [hde, if_neg hsym, if_neg hneob, dif_neg hhc]
    rw [goCur, dif_neg hrc, dif_neg hlit]
    simp only [hde, if_neg hsym, if_neg hneob, dif_neg hhc]
    simp only [bind, Except.bind]
    cases htb : InflateBuf.takeBits bb c'
        (Inflate.lengthExtra[sym.toNat - 257]'(by rw [Inflate.lengthExtra_size]; omega)).toNat with
    | error e => rfl
    | ok pe =>
      obtain ⟨eb, bb2, c2⟩ := pe
      simp only []
      cases hde2 : HuffTree.decodeSymCanon distLD distTable maxBits bb2 c2 with
      | error e => rfl
      | ok pd =>
        obtain ⟨dsym, bb3, c3, dused⟩ := pd
        simp only []
        by_cases hdidx : dsym.toNat ≥ Inflate.distBase.size
        · simp only [dif_pos hdidx]
        · simp only [dif_neg hdidx]
          cases htb2 : InflateBuf.takeBits bb3 c3
              (Inflate.distExtra[dsym.toNat]'(by
                rw [Inflate.distExtra_size]
                simp only [Inflate.distBase_size, ge_iff_le, Nat.not_le] at hdidx; omega)).toNat with
          | error e => rfl
          | ok pd2 =>
            obtain ⟨deb, bb4, c4⟩ := pd2
            simp only []
            by_cases hz : Inflate.distBase[dsym.toNat].toNat + deb = 0
            · simp only [dif_pos hz]
            · by_cases hds : Inflate.distBase[dsym.toNat].toNat + deb > outPos.toNat
              · simp only [dif_neg hz, dif_pos hds]
              · simp only [dif_neg hz, dif_neg hds]
                have heblt : eb < 2 ^ (Inflate.lengthExtra[sym.toNat - 257]'(by
                    rw [Inflate.lengthExtra_size]; omega)).toNat :=
                  takeBits_lt bb c' _ (lengthExtra_lt_64 (sym.toNat - 257) (by
                    rw [Inflate.lengthExtra_size]; omega)) htb
                have hlen258 : Inflate.lengthBase[sym.toNat - 257].toNat + eb ≤ 258 :=
                  length_le_258 (sym.toNat - 257) (by rw [Inflate.lengthBase_size]; omega) heblt
                rw [dif_neg (show ¬ Inflate.lengthBase[sym.toNat - 257].toNat + eb > 258 by omega)]
                rw [if_neg (show ¬ outPos.toNat + (Inflate.lengthBase[sym.toNat - 257].toNat + eb)
                  > maxOut by omega)]
                by_cases hnp : cnt.toNat ≤ c4
                · simp only [dif_pos hnp]
                · rw [dif_neg hnp, dif_neg hnp]
                  rw [ByteArray.copyWithinAtShort_if_eq]
                  have hrec := ih eb dsym hdidx deb bb4 c4 hds hnp (by
                    rw [ByteArray.copyWithinAtShort_if_eq, copyWithinAt_size]
                    exact hsize)
                  simpa only [ByteArray.copyWithinAtShort_if_eq] using hrec
  | case9 pos bitBuf cnt output outPos hrc hm =>
    intro hsize
    rw [InflateBuf.goCurU, dif_neg hrc, dif_neg hm]

/-- `goCurU` may be entered either before or after its byte refill: running the
    whole canonical refill up front does not change the result. -/
theorem goCurU_absorb_refill (litTable distTable : HuffTree.DecodeTable)
    (litLD distLD : HuffTree.LongDecode) (maxBits : Nat) (data : ByteArray)
    (maxOut : Nat) (hsz : data.size < USize.size)
    (hlp : litTable.packed.size = 2 ^ HuffTree.fastBits)
    (pos : USize) (bitBuf : UInt64) (cnt : USize) (output : ByteArray) (outPos : USize)
    (hpos : pos.toNat ≤ data.size) (hcnt : cnt.toNat ≤ 64) :
    let r := InflateBuf.refill data pos.toNat bitBuf cnt.toNat
    InflateBuf.goCurU litTable distTable litLD distLD maxBits data maxOut
        pos bitBuf cnt hsz hlp output outPos =
      InflateBuf.goCurU litTable distTable litLD distLD maxBits data maxOut
        r.1.toUSize r.2.1 r.2.2.toUSize hsz hlp output outPos := by
  rw [InflateBuf.refill]
  split
  · rename_i hrc
    have hpU : pos.toNat.toUSize = pos := by
      apply USize.toNat_inj.mp
      rw [InflateBuf.toUSize_toNat_of_lt (Nat.lt_of_le_of_lt hpos hsz)]
    have hcU : cnt.toNat.toUSize = cnt := by
      apply USize.toNat_inj.mp
      rw [InflateBuf.toUSize_toNat_of_lt (Nat.lt_of_le_of_lt hcnt
        (Nat.lt_of_lt_of_le (by decide) USize.le_size))]
    have hguard : cnt ≤ 56 ∧ pos < data.size.toUSize := by
      rw [← hpU, ← hcU,
        InflateBuf.refillGuard_usize data pos.toNat.toUSize cnt.toNat.toUSize hsz]
      simpa using hrc
    rw [InflateBuf.goCurU, dif_pos hguard,
      InflateBuf.uget_eq_getElem! data pos hrc.2]
    have hp1 : (pos + 1).toNat = pos.toNat + 1 := by
      rw [USize.toNat_add]
      have h1 : (1 : USize).toNat = 1 :=
        USize.toNat_ofNat_of_lt (Nat.lt_of_lt_of_le (by decide) USize.le_size)
      rw [h1]
      apply Nat.mod_eq_of_lt
      rw [← USize.size_eq_two_pow]
      omega
    have hc1 : (cnt + 8).toNat = cnt.toNat + 8 := by
      rw [USize.toNat_add]
      have h8 : (8 : USize).toNat = 8 :=
        USize.toNat_ofNat_of_lt (Nat.lt_of_lt_of_le (by decide) USize.le_size)
      rw [h8]
      apply Nat.mod_eq_of_lt
      rw [← USize.size_eq_two_pow]
      have : (64 : Nat) < USize.size := USize.size_eq_two_pow ▸
        Nat.lt_of_lt_of_le (by decide) USize.le_size
      omega
    have hstep := goCurU_absorb_refill litTable distTable litLD distLD maxBits data maxOut hsz hlp
      (pos + 1) (bitBuf ||| data[pos.toNat]!.toUInt64 <<< cnt.toUInt64) (cnt + 8)
      output outPos (by rw [hp1]; omega) (by rw [hc1]; omega)
    rw [InflateBuf.usize_toUInt64_toNat cnt] at hstep
    rw [← getElem!_pos data pos.toNat hrc.2]
    rw [InflateBuf.usize_toUInt64_toNat cnt]
    simpa only [hp1, hc1] using hstep
  · rename_i hrc
    have hpU : pos.toNat.toUSize = pos := by
      apply USize.toNat_inj.mp
      rw [InflateBuf.toUSize_toNat_of_lt (Nat.lt_of_le_of_lt hpos hsz)]
    have hcU : cnt.toNat.toUSize = cnt := by
      apply USize.toNat_inj.mp
      rw [InflateBuf.toUSize_toNat_of_lt (Nat.lt_of_le_of_lt hcnt
        (Nat.lt_of_lt_of_le (by decide) USize.le_size))]
    have hguard : ¬(cnt ≤ 56 ∧ pos < data.size.toUSize) := by
      intro h
      apply hrc
      exact (InflateBuf.refillGuard_usize data pos cnt hsz).mp h
    rw [InflateBuf.goCurU, dif_neg hguard]
    simp only
    rw [hpU, hcU]
    rw [InflateBuf.goCurU, dif_neg hguard]
termination_by data.size - pos.toNat
decreasing_by
  simp_wf
  have hlt : pos.toNat < data.size := by omega
  have hp : pos.toNat + 1 < 2 ^ System.Platform.numBits := by
    rw [← USize.size_eq_two_pow]
    exact Nat.lt_of_le_of_lt (Nat.succ_le_of_lt hlt) hsz
  rw [Nat.mod_eq_of_lt hp]
  omega

theorem goCurU_absorb_wide (litTable distTable : HuffTree.DecodeTable)
    (litLD distLD : HuffTree.LongDecode) (data : ByteArray) (maxOut : Nat)
    (hsz : data.size < USize.size)
    (hlp : litTable.packed.size = 2 ^ HuffTree.fastBits)
    {bitpos p0 p1 : Nat} {b0 b1 : UInt64} {c0 c1 a0 a1 : Nat}
    (h0 : InflateBuf.WideBufCorr data bitpos p0 b0 c0 a0)
    (h1 : InflateBuf.WideBufCorr data bitpos p1 b1 c1 a1)
    (hfull : 56 < c1 ∨ p1 = data.size)
    (output : ByteArray) (outPos : USize) :
    InflateBuf.goCurU litTable distTable litLD distLD 15 data maxOut
        p0.toUSize (InflateBuf.trimBits b0 c0) c0.toUSize hsz hlp output outPos =
      InflateBuf.goCurU litTable distTable litLD distLD 15 data maxOut
        p1.toUSize (InflateBuf.trimBits b1 c1) c1.toUSize hsz hlp output outPos := by
  have hp0 : p0.toUSize.toNat = p0 :=
    InflateBuf.toUSize_toNat_of_lt (Nat.lt_of_le_of_lt h0.posLe hsz)
  have hc0 : c0.toUSize.toNat = c0 :=
    InflateBuf.toUSize_toNat_of_lt (Nat.lt_of_le_of_lt
      (Nat.le_trans h0.cntLe h0.availLe)
      (Nat.lt_of_lt_of_le (by decide) USize.le_size))
  have h := goCurU_absorb_refill litTable distTable litLD distLD 15 data maxOut hsz hlp
    p0.toUSize (InflateBuf.trimBits b0 c0) c0.toUSize output outPos
    (by rw [hp0]; exact h0.posLe) (by rw [hc0]; exact Nat.le_trans h0.cntLe h0.availLe)
  rw [hp0, hc0, InflateBuf.refill_eq_trimmed_full h0 h1 hfull] at h
  have hp1 : p1.toUSize = p1.toUSize := rfl
  simpa only using h

theorem goCurU_absorb_wideU (litTable distTable : HuffTree.DecodeTable)
    (litLD distLD : HuffTree.LongDecode) (data : ByteArray) (maxOut : Nat)
    (hsz : data.size < USize.size)
    (hlp : litTable.packed.size = 2 ^ HuffTree.fastBits)
    {bitpos : Nat} {p0 p1 : USize} {b0 b1 : UInt64} {c0 c1 : USize} {a0 a1 : Nat}
    (h0 : InflateBuf.WideBufCorr data bitpos p0.toNat b0 c0.toNat a0)
    (h1 : InflateBuf.WideBufCorr data bitpos p1.toNat b1 c1.toNat a1)
    (hfull : 56 < c1.toNat ∨ p1.toNat = data.size)
    (output : ByteArray) (outPos : USize) :
    InflateBuf.goCurU litTable distTable litLD distLD 15 data maxOut
        p0 (InflateBuf.trimBits b0 c0.toNat) c0 hsz hlp output outPos =
      InflateBuf.goCurU litTable distTable litLD distLD 15 data maxOut
        p1 (InflateBuf.trimBits b1 c1.toNat) c1 hsz hlp output outPos := by
  have hp0 : p0.toNat.toUSize = p0 := by
    apply USize.toNat_inj.mp
    rw [InflateBuf.toUSize_toNat_of_lt (Nat.lt_of_le_of_lt h0.posLe hsz)]
  have hp1 : p1.toNat.toUSize = p1 := by
    apply USize.toNat_inj.mp
    rw [InflateBuf.toUSize_toNat_of_lt (Nat.lt_of_le_of_lt h1.posLe hsz)]
  have hc0 : c0.toNat.toUSize = c0 := by
    apply USize.toNat_inj.mp
    rw [InflateBuf.toUSize_toNat_of_lt (Nat.lt_of_le_of_lt
      (Nat.le_trans h0.cntLe h0.availLe)
      (Nat.lt_of_lt_of_le (by decide) USize.le_size))]
  have hc1 : c1.toNat.toUSize = c1 := by
    apply USize.toNat_inj.mp
    rw [InflateBuf.toUSize_toNat_of_lt (Nat.lt_of_le_of_lt
      (Nat.le_trans h1.cntLe h1.availLe)
      (Nat.lt_of_lt_of_le (by decide) USize.le_size))]
  simpa only [hp0, hp1, hc0, hc1] using
    goCurU_absorb_wide litTable distTable litLD distLD data maxOut hsz hlp
      h0 h1 hfull output outPos

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- The word-refill loop observes only counted stream bits. With production
    (15-bit) tables it therefore agrees with `goCurU` on the trimmed buffer. -/
theorem goCurUW_eq (litTable distTable : HuffTree.DecodeTable)
    (litLD distLD : HuffTree.LongDecode) (data : ByteArray) (maxOut : Nat)
    (hsz : data.size < USize.size)
    (hlp : litTable.packed.size = 2 ^ HuffTree.fastBits)
    (hlitFast : ∀ b : UInt64,
      (litTable.lenAt (b &&& 0x7FF).toNat).toNat ≤ HuffTree.fastBits)
    (hlitUsed : ∀ b n s bb c used,
      HuffTree.decodeSymCanon litLD litTable 15 b n = .ok (s, bb, c, used) → used ≤ 15)
    (hdistUsed : ∀ b n s bb c used,
      HuffTree.decodeSymCanon distLD distTable 15 b n = .ok (s, bb, c, used) → used ≤ 15) :
    ∀ (pos : USize) (bitBuf : UInt64) (cnt : USize)
      (output : ByteArray) (outPos : USize) (bitpos avail : Nat),
    InflateBuf.WideBufCorr data bitpos pos.toNat bitBuf cnt.toNat avail →
    output.size ≤ maxOut →
    InflateBuf.goCurUW litTable distTable litLD distLD 15 data maxOut
        pos bitBuf cnt hsz hlp output outPos =
      InflateBuf.goCurU litTable distTable litLD distLD 15 data maxOut
        pos (InflateBuf.trimBits bitBuf cnt.toNat) cnt hsz hlp output outPos := by
  intro pos bitBuf cnt output outPos
  induction pos, bitBuf, cnt, output, outPos using InflateBuf.goCurUW.induct
      (litTable := litTable) (litLD := litLD) (maxBits := 15)
      (data := data) (hsz := hsz) (hlp := hlp) with
  | case1 pos bitBuf cnt output outPos hmt r hwm pos1 bitBuf1 cnt1 didWide hrc ih =>
    intro bitpos avail hw hsize
    have hfalse : (InflateBuf.wideRefillU data pos bitBuf cnt hsz).didWide = false := by
      simpa only [r, didWide] using hrc.1
    have hrid : InflateBuf.wideRefillU data pos bitBuf cnt hsz =
        { pos := pos, bitBuf := bitBuf, cnt := cnt, didWide := false } := by
      simp only [InflateBuf.wideRefillU] at hfalse
      split at hfalse
      · contradiction
      · rename_i hn
        simp only [InflateBuf.wideRefillU, dif_neg hn]
    have hrc' : cnt ≤ 56 ∧ pos < data.size.toUSize := by
      simpa only [r, pos1, cnt1, hrid] using hrc.2
    obtain ⟨avail1, hwr⟩ := InflateBuf.wideRefillU_corr pos cnt hsz hw
    have hrcN : r.cnt.toNat ≤ 56 ∧ r.pos.toNat < data.size := by
      exact (InflateBuf.refillGuard_usize data r.pos r.cnt hsz).mp
        (by simpa only [pos1, cnt1] using hrc.2)
    have hp : (r.pos + 1).toNat = r.pos.toNat + 1 := by
      rw [USize.toNat_add, USize.toNat_one]
      apply Nat.mod_eq_of_lt
      rw [← USize.size_eq_two_pow]
      have hplt : r.pos.toNat < USize.size := Nat.lt_trans hrcN.2 hsz
      omega
    have h8 : (8 : USize).toNat = 8 :=
      USize.toNat_ofNat_of_lt (Nat.lt_of_lt_of_le (by decide) USize.le_size)
    have hc : (r.cnt + 8).toNat = r.cnt.toNat + 8 := by
      rw [USize.toNat_add, h8]
      apply Nat.mod_eq_of_lt
      rw [← USize.size_eq_two_pow]
      have hc64 := Nat.le_trans hwr.cntLe hwr.availLe
      have h64sz : (64 : Nat) < USize.size :=
        Nat.lt_of_lt_of_le (by decide) USize.le_size
      omega
    have hbyte := hwr.refillByte hrcN.1 hrcN.2
    have hread : data.uget r.pos (by
        have h := USize.lt_iff_toNat_lt.mp (show r.pos < data.size.toUSize by
          simpa only [pos1] using hrc.2.2)
        rwa [InflateBuf.toUSize_toNat_of_lt hsz] at h) = data[pos.toNat]! :=
      (InflateBuf.uget_eq_getElem! data r.pos hrcN.2).trans (by simp only [r, hrid])
    have hI := ih bitpos (r.cnt.toNat + 8) (by
      rw [hp, hc, InflateBuf.usize_toUInt64_toNat,
        InflateBuf.uget_eq_getElem! data r.pos hrcN.2]
      exact hbyte.toWide) hsize
    have hp0 : (pos + 1).toNat = pos.toNat + 1 := by
      simpa only [r, hrid] using hp
    have hc0 : (cnt + 8).toNat = cnt.toNat + 8 := by
      simpa only [r, hrid] using hc
    have hrcN0 := (InflateBuf.refillGuard_usize data pos cnt hsz).mp hrc'
    have hget0 := InflateBuf.uget_eq_getElem! data pos hrcN0.2
    have hI0 :
        InflateBuf.goCurUW litTable distTable litLD distLD 15 data maxOut
            (pos + 1) (bitBuf ||| data[pos.toNat]!.toUInt64 <<< cnt.toNat.toUInt64)
            (cnt + 8) hsz hlp output outPos =
          InflateBuf.goCurU litTable distTable litLD distLD 15 data maxOut
            (pos + 1) (InflateBuf.trimBits
              (bitBuf ||| data[pos.toNat]!.toUInt64 <<< cnt.toNat.toUInt64)
              (cnt.toNat + 8)) (cnt + 8) hsz hlp output outPos := by
      simpa only [r, pos1, bitBuf1, cnt1, hrid, hp0, hc0,
        InflateBuf.usize_toUInt64_toNat, hget0] using hI
    have hbyte0 := hw.refillByte hrcN0.1 hrcN0.2
    have heq : InflateBuf.trimBits
        (bitBuf ||| data[pos.toNat]!.toUInt64 <<< cnt.toNat.toUInt64) (cnt.toNat + 8) =
        InflateBuf.trimBits bitBuf cnt.toNat |||
          data[pos.toNat]!.toUInt64 <<< cnt.toNat.toUInt64 := by
      rw [InflateBuf.trimBits_eq_self hbyte0.cntLe hbyte0.high]
      exact (InflateBuf.BufCorr.bitBuf_eq hbyte0
        (InflateBuf.refill_step hw.trim hrcN0.1 hrcN0.2))
    rw [heq] at hI0
    rw [InflateBuf.goCurUW, dif_pos hmt]
    rw [dif_pos (by simpa only [r, pos1, bitBuf1, cnt1, didWide] using hrc)]
    simp only [hrid]
    rw [InflateBuf.goCurU, dif_pos hrc']
    rw [hget0, InflateBuf.usize_toUInt64_toNat]
    exact hI0
  | case2 pos bitBuf cnt output outPos hmt r hwm pos1 bitBuf1 cnt1 didWide hrc ent hlit ih =>
    intro bitpos avail hw hsize
    obtain ⟨avail1, hwr, hfull⟩ := InflateBuf.wideRefillU_full_of_no_tail
      pos cnt hsz hw (by simpa only [r, pos1, bitBuf1, cnt1, didWide] using hrc)
    have halign := goCurU_absorb_wideU litTable distTable litLD distLD data maxOut
      hsz hlp hw hwr hfull output outPos
    have hroot := hwr.trim_and_0x7FF hfull
    have hent : litTable.entryAtU
        (InflateBuf.trimBits r.bitBuf r.cnt.toNat &&& 0x7FF).toUSize
          (by rw [hlp]; exact HuffTree.and_0x7FF_toUSize_toNat_lt _) = ent := by
      dsimp only [ent, r, bitBuf1]
      congr 2
      exact (congrArg UInt64.toUSize hroot).trans
        (HuffTree.and_0x7FF_toUSize_eq_toUSize_and r.bitBuf)
    obtain ⟨hne, hle, hs⟩ := hlit
    have hk : (HuffTree.unpackLen ent).toNat ≤ r.cnt.toNat := by
      have := USize.le_iff_toNat_le.mp hle
      rwa [UInt8.toNat_toUSize] at this
    have hue : ent = litTable.entryAt (r.bitBuf &&& 0x7FF).toNat := by
      dsimp only [ent, r, bitBuf1]
      exact litTable.entryAtU_native_window_eq _ _
    have hk11 : (HuffTree.unpackLen ent).toNat ≤ 11 := by
      have ht := hlitFast r.bitBuf
      rw [litTable.lenAt_eq_unpackLen_entryAt, ← hue] at ht
      simpa only [HuffTree.fastBits] using ht
    have hcons := hwr.consume hk (by omega : (HuffTree.unpackLen ent).toNat < 64)
    have hsub : (r.cnt - (HuffTree.unpackLen ent).toUSize).toNat =
        r.cnt.toNat - (HuffTree.unpackLen ent).toNat := by
      rw [USize.toNat_sub_of_le _ _ hle, UInt8.toNat_toUSize]
    have hI := ih (bitpos + (HuffTree.unpackLen ent).toNat)
      (avail1 - (HuffTree.unpackLen ent).toNat) (by
        simpa only [r, pos1, bitBuf1, cnt1, hsub, InflateBuf.uint8_toUInt64_toNat] using hcons)
      (by rw [ByteArray.uset_eq_set!, ByteArray.size_set!]; exact hsize)
    rw [InflateBuf.goCurUW, dif_pos hmt]
    rw [dif_neg (by simpa only [r, pos1, bitBuf1, cnt1, didWide] using hrc),
      dif_pos ⟨hne, hle, hs⟩]
    rw [halign, InflateBuf.goCurU, dif_pos hmt,
      dif_neg (InflateBuf.refillGuard_usize_false_of_full data r.pos r.cnt hsz hfull)]
    rw [hent, dif_pos ⟨hne, hle, hs⟩]
    have hshift := InflateBuf.trimBits_shiftRight r.bitBuf
      (Nat.le_trans hwr.cntLe hwr.availLe) hk (by omega : (HuffTree.unpackLen ent).toNat < 64)
    simpa only [r, pos1, bitBuf1, cnt1, ent, hsub, hshift,
      InflateBuf.uint8_toUInt64_toNat,
      ByteArray.uset_eq_set!] using hI
  | case3 pos bitBuf cnt output outPos hmt r hwm pos1 bitBuf1 cnt1 didWide hrc ent hlit estr hde =>
    intro bitpos avail hw hsize
    dsimp only [bitBuf1, cnt1, r] at hde
    obtain ⟨avail1, hwr, hfull⟩ := InflateBuf.wideRefillU_full_of_no_tail
      pos cnt hsz hw (by simpa only [r, pos1, bitBuf1, cnt1, didWide] using hrc)
    have halign := goCurU_absorb_wideU litTable distTable litLD distLD data maxOut
      hsz hlp hw hwr hfull output outPos
    have hroot := hwr.trim_and_0x7FF hfull
    have hent : litTable.entryAtU
        (InflateBuf.trimBits r.bitBuf r.cnt.toNat &&& 0x7FF).toUSize
          (by rw [hlp]; exact HuffTree.and_0x7FF_toUSize_toNat_lt _) = ent := by
      dsimp only [ent, r, bitBuf1]
      congr 2
      exact (congrArg UInt64.toUSize hroot).trans
        (HuffTree.and_0x7FF_toUSize_eq_toUSize_and r.bitBuf)
    have hmap := hwr.decodeSymCanon_map_trim (hfull.imp (by omega) id) litLD litTable
    have hde' : HuffTree.decodeSymCanon litLD litTable 15
        (InflateBuf.trimBits r.bitBuf r.cnt.toNat) r.cnt.toNat = .error estr := by
      cases hx : HuffTree.decodeSymCanon litLD litTable 15
          (InflateBuf.trimBits r.bitBuf r.cnt.toNat) r.cnt.toNat with
      | error e =>
        rw [hx, hde] at hmap
        simp only [Except.map, Except.error.injEq] at hmap
        subst e
        simpa only using hx
      | ok x =>
        rw [hx, hde] at hmap
        contradiction
    dsimp only [r] at hde'
    rw [InflateBuf.goCurUW, dif_pos hmt,
      dif_neg (by simpa only [r, pos1, bitBuf1, cnt1, didWide] using hrc), dif_neg hlit]
    simp only [hde]
    rw [halign, InflateBuf.goCurU, dif_pos hmt,
      dif_neg (InflateBuf.refillGuard_usize_false_of_full data r.pos r.cnt hsz hfull),
      hent, dif_neg hlit]
    simp only [hde']
  | case4 pos bitBuf cnt output outPos hmt r hwm pos1 bitBuf1 cnt1 didWide hrc ent hlit
      cnt0 sym bb c used hde hsym hnp =>
    intro bitpos avail hw hsize
    dsimp only [bitBuf1, cnt1, r] at hde
    obtain ⟨avail1, hwr, hfull⟩ := InflateBuf.wideRefillU_full_of_no_tail
      pos cnt hsz hw (by simpa only [r, pos1, bitBuf1, cnt1, didWide] using hrc)
    have halign := goCurU_absorb_wideU litTable distTable litLD distLD data maxOut
      hsz hlp hw hwr hfull output outPos
    have hroot := hwr.trim_and_0x7FF hfull
    have hent : litTable.entryAtU
        (InflateBuf.trimBits r.bitBuf r.cnt.toNat &&& 0x7FF).toUSize
          (by rw [hlp]; exact HuffTree.and_0x7FF_toUSize_toNat_lt _) = ent := by
      dsimp only [ent, r, bitBuf1]
      congr 2
      exact (congrArg UInt64.toUSize hroot).trans
        (HuffTree.and_0x7FF_toUSize_eq_toUSize_and r.bitBuf)
    have hde' := hwr.decodeSymCanon_trim_ok (hfull.imp (by omega) id) litLD litTable
      (by have := hlitUsed r.bitBuf r.cnt.toNat sym bb c used hde; omega) hde
    rw [InflateBuf.goCurUW, dif_pos hmt,
      dif_neg (by simpa only [r, pos1, bitBuf1, cnt1, didWide] using hrc), dif_neg hlit]
    simp only [hde]
    rw [if_pos hsym, dif_pos hnp]
    rw [halign, InflateBuf.goCurU, dif_pos hmt,
      dif_neg (InflateBuf.refillGuard_usize_false_of_full data r.pos r.cnt hsz hfull),
      hent, dif_neg hlit]
    simp only [hde']
    rw [if_pos hsym, dif_pos hnp]
  | case5 pos bitBuf cnt output outPos hmt r hwm pos1 bitBuf1 cnt1 didWide hrc ent hlit
      cnt0 sym bb c used hde hsym hnp ih =>
    intro bitpos avail hw hsize
    dsimp only [bitBuf1, cnt1, r] at hde
    obtain ⟨avail1, hwr, hfull⟩ := InflateBuf.wideRefillU_full_of_no_tail
      pos cnt hsz hw (by simpa only [r, pos1, bitBuf1, cnt1, didWide] using hrc)
    have halign := goCurU_absorb_wideU litTable distTable litLD distLD data maxOut
      hsz hlp hw hwr hfull output outPos
    have hroot := hwr.trim_and_0x7FF hfull
    have hent : litTable.entryAtU
        (InflateBuf.trimBits r.bitBuf r.cnt.toNat &&& 0x7FF).toUSize
          (by rw [hlp]; exact HuffTree.and_0x7FF_toUSize_toNat_lt _) = ent := by
      dsimp only [ent, r, bitBuf1]
      congr 2
      exact (congrArg UInt64.toUSize hroot).trans
        (HuffTree.and_0x7FF_toUSize_eq_toUSize_and r.bitBuf)
    have hde' := hwr.decodeSymCanon_trim_ok (hfull.imp (by omega) id) litLD litTable
      (by have := hlitUsed r.bitBuf r.cnt.toNat sym bb c used hde; omega) hde
    obtain ⟨hbb, hc, hu⟩ := InflateBuf.decodeSymCanon_ok_spec litLD litTable 15
      r.bitBuf r.cnt.toNat hde
    have hu15 := hlitUsed r.bitBuf r.cnt.toNat sym bb c used hde
    have hcons := hwr.consume hu (by omega : used < 64)
    rw [← hbb, ← hc] at hcons
    have hcle := HuffTree.decodeSymCanon_cnt_le litLD litTable 15
      r.bitBuf r.cnt.toNat hde
    have hcrt : c.toUSize.toNat = c := InflateBuf.toUSize_toNat_of_lt
      (Nat.lt_of_le_of_lt hcle (Nat.lt_of_le_of_lt
        (Nat.le_trans hwr.cntLe hwr.availLe)
        (Nat.lt_of_lt_of_le (by decide : 64 < 2 ^ 32) USize.le_size)))
    have hI := ih (bitpos + used) (avail1 - used)
      (by simpa only [r, pos1, hcrt] using hcons)
      (by rw [ByteArray.uset_eq_set!, ByteArray.size_set!]; exact hsize)
    rw [InflateBuf.goCurUW, dif_pos hmt,
      dif_neg (by simpa only [r, pos1, bitBuf1, cnt1, didWide] using hrc), dif_neg hlit]
    simp only [hde]
    rw [if_pos hsym, dif_neg hnp]
    rw [halign, InflateBuf.goCurU, dif_pos hmt,
      dif_neg (InflateBuf.refillGuard_usize_false_of_full data r.pos r.cnt hsz hfull),
      hent, dif_neg hlit]
    simp only [hde']
    rw [if_pos hsym, dif_neg hnp]
    simpa only [r, pos1, bitBuf1, cnt1, hcrt, ByteArray.uset_eq_set!] using hI
  | case6 pos bitBuf cnt output outPos hmt r hwm pos1 bitBuf1 cnt1 didWide hrc ent hlit
      sym bb c used hde hsym heob =>
    intro bitpos avail hw hsize
    dsimp only [bitBuf1, cnt1, r] at hde
    obtain ⟨avail1, hwr, hfull⟩ := InflateBuf.wideRefillU_full_of_no_tail
      pos cnt hsz hw (by simpa only [r, pos1, bitBuf1, cnt1, didWide] using hrc)
    have halign := goCurU_absorb_wideU litTable distTable litLD distLD data maxOut
      hsz hlp hw hwr hfull output outPos
    have hroot := hwr.trim_and_0x7FF hfull
    have hent : litTable.entryAtU
        (InflateBuf.trimBits r.bitBuf r.cnt.toNat &&& 0x7FF).toUSize
          (by rw [hlp]; exact HuffTree.and_0x7FF_toUSize_toNat_lt _) = ent := by
      dsimp only [ent, r, bitBuf1]
      congr 2
      exact (congrArg UInt64.toUSize hroot).trans
        (HuffTree.and_0x7FF_toUSize_eq_toUSize_and r.bitBuf)
    have hde' := hwr.decodeSymCanon_trim_ok (hfull.imp (by omega) id) litLD litTable
      (by have := hlitUsed r.bitBuf r.cnt.toNat sym bb c used hde; omega) hde
    have hcle := HuffTree.decodeSymCanon_cnt_le litLD litTable 15 r.bitBuf r.cnt.toNat hde
    have hcrt : c.toUSize.toNat = c := InflateBuf.toUSize_toNat_of_lt
      (Nat.lt_of_le_of_lt hcle (Nat.lt_of_le_of_lt
        (Nat.le_trans hwr.cntLe hwr.availLe)
        (Nat.lt_of_lt_of_le (by decide : 64 < 2 ^ 32) USize.le_size)))
    rw [InflateBuf.goCurUW, dif_pos hmt,
      dif_neg (by simpa only [r, pos1, bitBuf1, cnt1, didWide] using hrc), dif_neg hlit]
    simp only [hde]
    rw [if_neg hsym, if_pos heob,
      InflateBuf.trimBitBufU_eq_trimBits bb c.toUSize (by
        rw [hcrt]
        exact Nat.le_trans hcle (Nat.le_trans hwr.cntLe hwr.availLe)), hcrt]
    rw [halign, InflateBuf.goCurU, dif_pos hmt,
      dif_neg (InflateBuf.refillGuard_usize_false_of_full data r.pos r.cnt hsz hfull),
      hent, dif_neg hlit]
    simp only [hde']
    rw [if_neg hsym, if_pos heob]
  | case7 pos bitBuf cnt output outPos hmt r hwm pos1 bitBuf1 cnt1 didWide hrc ent hlit
      sym bb c used hde hsym hneob idx hidx =>
    intro bitpos avail hw hsize
    dsimp only [bitBuf1, cnt1, r] at hde
    obtain ⟨avail1, hwr, hfull⟩ := InflateBuf.wideRefillU_full_of_no_tail
      pos cnt hsz hw (by simpa only [r, pos1, bitBuf1, cnt1, didWide] using hrc)
    have halign := goCurU_absorb_wideU litTable distTable litLD distLD data maxOut
      hsz hlp hw hwr hfull output outPos
    have hroot := hwr.trim_and_0x7FF hfull
    have hent : litTable.entryAtU
        (InflateBuf.trimBits r.bitBuf r.cnt.toNat &&& 0x7FF).toUSize
          (by rw [hlp]; exact HuffTree.and_0x7FF_toUSize_toNat_lt _) = ent := by
      dsimp only [ent, r, bitBuf1]
      congr 2
      exact (congrArg UInt64.toUSize hroot).trans
        (HuffTree.and_0x7FF_toUSize_eq_toUSize_and r.bitBuf)
    have hde' := hwr.decodeSymCanon_trim_ok (hfull.imp (by omega) id) litLD litTable
      (by have := hlitUsed r.bitBuf r.cnt.toNat sym bb c used hde; omega) hde
    rw [InflateBuf.goCurUW, dif_pos hmt,
      dif_neg (by simpa only [r, pos1, bitBuf1, cnt1, didWide] using hrc), dif_neg hlit]
    simp only [hde]
    rw [if_neg hsym, if_neg hneob, dif_pos hidx]
    rw [halign, InflateBuf.goCurU, dif_pos hmt,
      dif_neg (InflateBuf.refillGuard_usize_false_of_full data r.pos r.cnt hsz hfull),
      hent, dif_neg hlit]
    simp only [hde']
    rw [if_neg hsym, if_neg hneob, dif_pos hidx]
  | case8 pos bitBuf cnt output outPos hmt r hwm pos1 bitBuf1 cnt1 didWide hrc ent hlit
      cnt0 sym bb c used hde hsym hneob idx hh base ih =>
    intro bitpos avail hw hsize
    dsimp only [bitBuf1, cnt1, r] at hde
    obtain ⟨avail1, hwr, hfull⟩ := InflateBuf.wideRefillU_full_of_no_tail
      pos cnt hsz hw (by simpa only [r, pos1, bitBuf1, cnt1, didWide] using hrc)
    have halign := goCurU_absorb_wideU litTable distTable litLD distLD data maxOut
      hsz hlp hw hwr hfull output outPos
    have hroot := hwr.trim_and_0x7FF hfull
    have hent : litTable.entryAtU
        (InflateBuf.trimBits r.bitBuf r.cnt.toNat &&& 0x7FF).toUSize
          (by rw [hlp]; exact HuffTree.and_0x7FF_toUSize_toNat_lt _) = ent := by
      dsimp only [ent, r, bitBuf1]
      congr 2
      exact (congrArg UInt64.toUSize hroot).trans
        (HuffTree.and_0x7FF_toUSize_eq_toUSize_and r.bitBuf)
    have hde' := hwr.decodeSymCanon_trim_ok (hfull.imp (by omega) id) litLD litTable
      (by have := hlitUsed r.bitBuf r.cnt.toNat sym bb c used hde; omega) hde
    obtain ⟨hbb, hc, hu⟩ := InflateBuf.decodeSymCanon_ok_spec litLD litTable 15
      r.bitBuf r.cnt.toNat hde
    have hu15 := hlitUsed r.bitBuf r.cnt.toNat sym bb c used hde
    have hw1 := hwr.consume hu (by omega : used < 64)
    rw [← hbb, ← hc] at hw1
    have hidxLen : sym.toNat - 257 < Inflate.lengthBase.size := by omega
    have hidxExtra : sym.toNat - 257 < Inflate.lengthExtra.size := by
      rw [Inflate.lengthExtra_size, ← Inflate.lengthBase_size]
      exact hidxLen
    have hhc : ¬ sym.toNat - 257 ≥ Inflate.lengthBase.size := by omega
    rw [InflateBuf.goCurUW, dif_pos hmt,
      dif_neg (by simpa only [r, pos1, bitBuf1, cnt1, didWide] using hrc), dif_neg hlit]
    simp only [hde]
    rw [if_neg hsym, if_neg hneob, dif_neg hhc]
    rw [halign, InflateBuf.goCurU, dif_pos hmt,
      dif_neg (InflateBuf.refillGuard_usize_false_of_full data r.pos r.cnt hsz hfull),
      hent, dif_neg hlit]
    simp only [hde']
    rw [if_neg hsym, if_neg hneob, dif_neg hhc]
    simp only [bind, Except.bind]
    cases htb : InflateBuf.takeBits bb c
        (Inflate.lengthExtra[sym.toNat - 257]'hidxExtra).toNat with
    | error e =>
      have htb' : InflateBuf.takeBits (InflateBuf.trimBits bb c) c
          (Inflate.lengthExtra[sym.toNat - 257]'hidxExtra).toNat = .error e :=
        InflateBuf.takeBits_trim_error bb c _ htb
      simp only [htb, htb']
    | ok pe =>
      obtain ⟨eb, bb2, c2⟩ := pe
      obtain ⟨hn, hbb2, hc2⟩ := InflateBuf.takeBits_ok_spec bb c
        (Inflate.lengthExtra[sym.toNat - 257]'hidxExtra).toNat htb
      have hn64 := lengthExtra_lt_64 (sym.toNat - 257)
        hidxExtra
      have htb' := InflateBuf.takeBits_trim_ok bb c
        (Inflate.lengthExtra[sym.toNat - 257]'hidxExtra).toNat
        hn hn64 (Nat.le_trans hw1.cntLe hw1.availLe) htb
      have hw2 := hw1.consume hn hn64
      rw [← hbb2, ← hc2] at hw2
      have hposfull2 : 15 ≤ c2 ∨ r.pos.toNat = data.size := by
        rcases hfull with hf | hp
        · left
          have hf' : 56 < r.cnt.toNat := by simpa only [r] using hf
          have hn5 : (Inflate.lengthExtra[sym.toNat - 257]'hidxExtra).toNat ≤ 5 :=
            lengthExtra_le_5 _ hidxExtra
          have hc2eq : c2 = r.cnt.toNat -
              (used + (Inflate.lengthExtra[sym.toNat - 257]'hidxExtra).toNat) := by
            rw [hc2, hc, Nat.sub_sub]
          rw [hc2eq]
          apply Nat.le_sub_of_add_le
          omega
        · right; exact hp
      simp only [htb, htb']
      cases hdd : HuffTree.decodeSymCanon distLD distTable 15 bb2 c2 with
      | error e =>
        have hm := hw2.decodeSymCanon_map_trim hposfull2 distLD distTable
        have hdd' : HuffTree.decodeSymCanon distLD distTable 15
            (InflateBuf.trimBits bb2 c2) c2 = .error e := by
          cases hx : HuffTree.decodeSymCanon distLD distTable 15
              (InflateBuf.trimBits bb2 c2) c2 with
          | error e' =>
            rw [hx, hdd] at hm
            simp only [Except.map, Except.error.injEq] at hm
            subst e'
            simpa only using hx
          | ok x => rw [hx, hdd] at hm; contradiction
        simp only [hdd, hdd']
      | ok pd =>
        obtain ⟨dsym, bb3, c3, dused⟩ := pd
        have hdd' := hw2.decodeSymCanon_trim_ok hposfull2 distLD distTable
          (by have := hdistUsed bb2 c2 dsym bb3 c3 dused hdd; omega) hdd
        obtain ⟨hbb3, hc3, hdu⟩ := InflateBuf.decodeSymCanon_ok_spec
          distLD distTable 15 bb2 c2 hdd
        have hdu15 := hdistUsed bb2 c2 dsym bb3 c3 dused hdd
        have hw3 := hw2.consume hdu (by omega : dused < 64)
        rw [← hbb3, ← hc3] at hw3
        simp only [hdd, hdd']
        by_cases hdidx : dsym.toNat ≥ Inflate.distBase.size
        · simp only [dif_pos hdidx]
        · simp only [dif_neg hdidx]
          have hdidxExtra : dsym.toNat < Inflate.distExtra.size := by
            rw [Inflate.distExtra_size, ← Inflate.distBase_size]
            omega
          cases htb2 : InflateBuf.takeBits bb3 c3
              (Inflate.distExtra[dsym.toNat]'hdidxExtra).toNat with
          | error e =>
            have htb2' : InflateBuf.takeBits (InflateBuf.trimBits bb3 c3) c3
                (Inflate.distExtra[dsym.toNat]'hdidxExtra).toNat = .error e :=
              InflateBuf.takeBits_trim_error bb3 c3 _ htb2
            simp only [htb2, htb2']
          | ok pd2 =>
            obtain ⟨deb, bb4, c4⟩ := pd2
            obtain ⟨hdn, hbb4, hc4⟩ := InflateBuf.takeBits_ok_spec bb3 c3
              (Inflate.distExtra[dsym.toNat]'hdidxExtra).toNat htb2
            have hdn64 := distExtra_lt_64 dsym.toNat
              hdidxExtra
            have htb2' := InflateBuf.takeBits_trim_ok bb3 c3
              (Inflate.distExtra[dsym.toNat]'hdidxExtra).toNat
              hdn hdn64 (Nat.le_trans hw3.cntLe hw3.availLe) htb2
            have hw4 := hw3.consume hdn hdn64
            rw [← hbb4, ← hc4] at hw4
            simp only [htb2, htb2']
            by_cases hz : Inflate.distBase[dsym.toNat].toNat + deb = 0
            · split
              · rfl
              · rename_i hnzero
                exact (hnzero hz).elim
            · split
              · rename_i hzero
                exact (hz hzero).elim
              · split
                · rfl
                · rename_i hds
                  have heblt : eb < 2 ^ (Inflate.lengthExtra[sym.toNat - 257]'hidxExtra).toNat :=
                    takeBits_lt bb c _ hn64 htb
                  have hlen258 : Inflate.lengthBase[sym.toNat - 257].toNat + eb ≤ 258 :=
                    length_le_258 (sym.toNat - 257)
                      hidxLen heblt
                  split
                  · rfl
                  · rename_i hlen
                    split
                    · rfl
                    · rename_i hnp
                      have hc4rt : c4.toUSize.toNat = c4 := InflateBuf.toUSize_toNat_of_lt
                        (Nat.lt_of_le_of_lt (Nat.le_trans hw4.cntLe hw4.availLe)
                          (Nat.lt_of_lt_of_le (by decide : 64 < 2 ^ 32) USize.le_size))
                      simpa only [r, pos1, base, idx, hc4rt, Nat.add_assoc] using
                        ih eb dsym hdidx deb bb4 c4 hds hnp
                          (bitpos + used +
                            (Inflate.lengthExtra[sym.toNat - 257]'hidxExtra).toNat +
                            dused + (Inflate.distExtra[dsym.toNat]'hdidxExtra).toNat)
                          (avail1 - used -
                            (Inflate.lengthExtra[sym.toNat - 257]'hidxExtra).toNat -
                            dused - (Inflate.distExtra[dsym.toNat]'hdidxExtra).toNat)
                          (by simpa only [r, pos1, hc4rt, Nat.add_assoc] using hw4)
                          (by
                            rw [ByteArray.copyWithinAtShort_if_eq, copyWithinAt_size]
                            exact hsize)
  | case9 pos bitBuf cnt output outPos hmt =>
    intro bitpos avail hw hsize
    rw [InflateBuf.goCurUW, dif_neg hmt,
      InflateBuf.trimBitBufU_eq_trimBits bitBuf cnt (Nat.le_trans hw.cntLe hw.availLe)]
    exact (goCurU_eq litTable distTable litLD distLD 15 data maxOut hsz hlp
      pos (InflateBuf.trimBits bitBuf cnt.toNat) cnt output outPos hsize).symm

/-- The `uset` fastloop block decoder agrees with the `set!` one (lifts `goCurU_eq`
    through the shared `decodeHuffmanCurTables` scaffolding). -/
theorem decodeHuffmanCurTablesU_eq (br : ZipCommon.BitReader) (output : ByteArray) (outPos : Nat)
    (litTable distTable : HuffTree.DecodeTable) (litLD distLD : HuffTree.LongDecode) (maxOut : Nat)
    (hlp : litTable.packed.size = 2 ^ HuffTree.fastBits)
    (hlitFast : ∀ b : UInt64,
      (litTable.lenAt (b &&& 0x7FF).toNat).toNat ≤ HuffTree.fastBits)
    (hlitUsed : ∀ b n s bb c used,
      HuffTree.decodeSymCanon litLD litTable 15 b n = .ok (s, bb, c, used) → used ≤ 15)
    (hdistUsed : ∀ b n s bb c used,
      HuffTree.decodeSymCanon distLD distTable 15 b n = .ok (s, bb, c, used) → used ≤ 15)
    (hwf : br.bitOff < 8) (hbp : br.bitPos ≤ br.data.size * 8)
    (hsize : output.size ≤ maxOut) :
    InflateBuf.decodeHuffmanCurTablesU br output outPos litTable distTable litLD distLD maxOut hlp
      = InflateBuf.decodeHuffmanCurTables br output outPos litTable distTable litLD distLD maxOut hlp := by
  unfold InflateBuf.decodeHuffmanCurTablesU InflateBuf.decodeHuffmanCurTables
  by_cases hszeq : br.data.size.toUSize.toNat = br.data.size
  · simp only [hszeq, ↓reduceDIte]
    have hsz : br.data.size < USize.size := by
      rw [← hszeq]
      exact USize.toNat_lt_two_pow_numBits _
    have hposle : br.pos ≤ br.data.size := by
      have hbpe : br.bitPos = br.pos * 8 + br.bitOff := rfl
      omega
    have hbc0 : InflateBuf.BufCorr br.data (br.pos * 8) br.pos 0 0 :=
      ⟨by omega, hposle, by omega, by simp, fun j hj => absurd hj (Nat.not_lt_zero j)⟩
    rcases hrf : InflateBuf.refill br.data br.pos 0 0 with ⟨p, b, c⟩
    obtain ⟨hbc1, hfull⟩ := InflateBuf.refill_corr hbc0 hrf
    have hboff : br.bitOff ≤ c := by
      rcases hfull with hc | hp
      · omega
      · have hs := hbc1.span; rw [hp] at hs
        have hbp' := hbp
        simp only [ZipCommon.BitReader.bitPos] at hbp'
        omega
    have hbc2 := InflateBuf.consume_corr hbc1 hboff (by omega : br.bitOff < 64)
    have hp : p.toUSize.toNat = p := InflateBuf.toUSize_toNat_of_lt
      (Nat.lt_of_le_of_lt hbc2.posLe hsz)
    have hc : (c - br.bitOff).toUSize.toNat = c - br.bitOff :=
      InflateBuf.toUSize_toNat_of_lt (Nat.lt_of_le_of_lt hbc2.cntLe
        (Nat.lt_of_lt_of_le (by decide) USize.le_size))
    have hw : InflateBuf.WideBufCorr br.data br.bitPos p.toUSize.toNat
        (b >>> br.bitOff.toUInt64) (c - br.bitOff).toUSize.toNat (c - br.bitOff) := by
      simpa only [ZipCommon.BitReader.bitPos, hp, hc] using hbc2.toWide
    have hwEq := goCurUW_eq litTable distTable litLD distLD br.data maxOut hsz hlp
      hlitFast hlitUsed hdistUsed p.toUSize (b >>> br.bitOff.toUInt64)
      (c - br.bitOff).toUSize output outPos.toUSize br.bitPos (c - br.bitOff) hw hsize
    have htrim : InflateBuf.trimBits (b >>> br.bitOff.toUInt64) (c - br.bitOff) =
        b >>> br.bitOff.toUInt64 :=
      InflateBuf.trimBits_eq_self hbc2.cntLe hbc2.high
    have hcurEq := goCurU_eq litTable distTable litLD distLD 15 br.data maxOut hsz hlp
      p.toUSize (b >>> br.bitOff.toUInt64)
      (c - br.bitOff).toUSize output outPos.toUSize hsize
    have hwEq' : InflateBuf.goCurUW litTable distTable litLD distLD 15 br.data maxOut
        p.toUSize (b >>> br.bitOff.toUInt64) (c - br.bitOff).toUSize hsz hlp output outPos.toUSize =
      InflateBuf.goCurU litTable distTable litLD distLD 15 br.data maxOut p.toUSize
        (b >>> br.bitOff.toUInt64)
        (c - br.bitOff).toUSize hsz hlp output outPos.toUSize := by
      simpa only [hc, htrim] using hwEq
    simp only
    rw [hwEq', hcurEq]
  · simp only [hszeq, ↓reduceDIte]


set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
/-- **The `uset` block loop agrees with the `set!` block loop.** Identical block
    dispatch and `BitReader` bookkeeping; the only per-block difference
    (`decodeHuffmanCurTablesU` vs `decodeHuffmanCurTables`) is bridged by
    `decodeHuffmanCurTablesU_eq`, and every block decoder preserves the buffer
    size, so the invariant `output.size ≤ maxOut` threads through the recursion. -/
theorem inflateLoopCurU_eq (maxOut dataSize : Nat) :
    ∀ (br : ZipCommon.BitReader) (output : ByteArray) (outPos : Nat),
    output.size ≤ maxOut →
    InflateBuf.inflateLoopCurU br output outPos maxOut dataSize
      = InflateBuf.inflateLoopCur br output outPos maxOut dataSize := by
  intro br output outPos
  induction br, output, outPos using InflateBuf.inflateLoopCurU.induct (dataSize := dataSize) with
  | case1 br output outPos ih =>
    intro hsize
    rw [InflateBuf.inflateLoopCurU, InflateBuf.inflateLoopCur]
    cases h1 : br.readBits 1 with
    | error e => simp only [h1, bind, Except.bind]
    | ok r1 =>
      obtain ⟨bfinal, br₁⟩ := r1
      cases h2 : br₁.readBits 2 with
      | error e => simp only [h1, h2, bind, Except.bind]
      | ok r2 =>
        obtain ⟨btype, br₂⟩ := r2
        have hbo₂ : br₂.bitOff < 8 := InflateBuf.readBits_bitOff_lt_pos (by omega) h2
        have hbp₂ : br₂.bitPos ≤ br₂.data.size * 8 := by
          exact Deflate.Correctness.readBits_bitPos_le br₁ 2 btype br₂ (by omega) h2
        have hflv : Huffman.Spec.ValidLengths
            (Inflate.fixedLitLengths.toList.map UInt8.toNat) 15 := by
          obtain ⟨fixedLit, hfl⟩ := Zip.Spec.DeflateStoredCorrect.fromLengths_fixedLit_ok
          exact Deflate.Correctness.fromLengths_valid Inflate.fixedLitLengths 15 fixedLit hfl
        have hfdv : Huffman.Spec.ValidLengths
            (Inflate.fixedDistLengths.toList.map UInt8.toNat) 15 := by
          obtain ⟨fixedDist, hfd⟩ := Zip.Spec.DeflateStoredCorrect.fromLengths_fixedDist_ok
          exact Deflate.Correctness.fromLengths_valid Inflate.fixedDistLengths 15 fixedDist hfd
        have hflFast : ∀ b : UInt64,
            (Inflate.fixedLitTF.1.lenAt (b &&& 0x7FF).toNat).toNat ≤ HuffTree.fastBits := by
          intro b
          simpa only [Inflate.fixedLitTF, Inflate.fixedLitCount] using
            treeFree_len_le Inflate.fixedLitLengths hflv (by decide) b
        have hflUsed : ∀ b n s bb c used,
            HuffTree.decodeSymCanon Inflate.fixedLitTF.2 Inflate.fixedLitTF.1 15 b n =
              .ok (s, bb, c, used) → used ≤ 15 := by
          intro b n s bb c used h
          simpa only [Inflate.fixedLitTF, Inflate.fixedLitCount] using
            treeFree_decode_used_le Inflate.fixedLitLengths hflv (by decide) h
        have hfdUsed : ∀ b n s bb c used,
            HuffTree.decodeSymCanon Inflate.fixedDistTF.2 Inflate.fixedDistTF.1 15 b n =
              .ok (s, bb, c, used) → used ≤ 15 := by
          intro b n s bb c used h
          simpa only [Inflate.fixedDistTF, Inflate.fixedDistCount] using
            treeFree_decode_used_le Inflate.fixedDistLengths hfdv (by decide) h
        have htail : ∀ (o' : ByteArray) (p' : Nat) (b' : ZipCommon.BitReader), o'.size ≤ maxOut →
            (if bfinal == 1 then (pure (o', p', b'.alignToByte.pos) : Except String (ByteArray × Nat × Nat))
             else if _h : b'.bitPos ≤ br.bitPos then throw "Inflate: no progress in inflate loop"
                  else if _h : dataSize * 8 < b'.bitPos then throw "Inflate: bit position out of range"
                  else InflateBuf.inflateLoopCurU b' o' p' maxOut dataSize)
          = (if bfinal == 1 then pure (o', p', b'.alignToByte.pos)
             else if _h : b'.bitPos ≤ br.bitPos then throw "Inflate: no progress in inflate loop"
                  else if _h : dataSize * 8 < b'.bitPos then throw "Inflate: bit position out of range"
                  else InflateBuf.inflateLoopCur b' o' p' maxOut dataSize) := by
          intro o' p' b' ho'
          by_cases hbf : (bfinal == 1) = true
          · rw [if_pos hbf, if_pos hbf]
          · rw [if_neg hbf, if_neg hbf]
            by_cases hg1 : b'.bitPos ≤ br.bitPos
            · rw [dif_pos hg1, dif_pos hg1]
            · rw [dif_neg hg1, dif_neg hg1]
              by_cases hg2 : dataSize * 8 < b'.bitPos
              · rw [dif_pos hg2, dif_pos hg2]
              · rw [dif_neg hg2, dif_neg hg2]; exact ih o' p' b' hg1 hg2 ho'
        have hbtv : btype = 0 ∨ btype = 1 ∨ btype = 2 ∨ btype = 3 := by
          have hb4 : btype.toNat < 4 := Inflate.readBits_lt (n := 2) (by omega) h2
          rcases (show btype.toNat = 0 ∨ btype.toNat = 1 ∨ btype.toNat = 2 ∨ btype.toNat = 3 from by omega)
            with h' | h' | h' | h'
          · exact Or.inl (UInt32.toNat_inj.mp (by rw [h']; rfl))
          · exact Or.inr (Or.inl (UInt32.toNat_inj.mp (by rw [h']; rfl)))
          · exact Or.inr (Or.inr (Or.inl (UInt32.toNat_inj.mp (by rw [h']; rfl))))
          · exact Or.inr (Or.inr (Or.inr (UInt32.toNat_inj.mp (by rw [h']; rfl))))
        simp only [h1, h2, bind, Except.bind]
        rcases hbtv with rfl | rfl | rfl | rfl
        · cases hb : InflateBuf.decodeStoredCur br₂ output outPos maxOut with
          | error e => simp only [hb, bind, Except.bind]
          | ok r =>
            obtain ⟨o', p', b'⟩ := r
            simp only [hb, bind, Except.bind]
            exact htail o' p' b' (by rw [decodeStoredCur_size hb]; exact hsize)
        · rw [decodeHuffmanCurTablesU_eq br₂ output outPos _ _ _ _ maxOut _
              hflFast hflUsed hfdUsed hbo₂ hbp₂ hsize]
          cases hb : InflateBuf.decodeHuffmanCurTables br₂ output outPos
              Inflate.fixedLitTF.1 Inflate.fixedDistTF.1 Inflate.fixedLitTF.2 Inflate.fixedDistTF.2 maxOut
              (HuffTree.buildTreeFreeWithCount_size Inflate.fixedLitLengths Inflate.fixedLitCount 15) with
          | error e => simp only [hb, bind, Except.bind]
          | ok r =>
            obtain ⟨o', p', b'⟩ := r
            simp only [hb, bind, Except.bind]
            exact htail o' p' b' (by rw [decodeHuffmanCurTables_size hb]; exact hsize)
        · cases hd : Inflate.decodeDynamicLengthsOnly br₂ with
          | error e => simp only [hd, bind, Except.bind]
          | ok rd =>
            obtain ⟨litLens, distLens, br₃⟩ := rd
            simp only [hd, bind, Except.bind]
            obtain ⟨hdyntrees, hlv, hdv, hlb, hdb⟩ := Inflate.decodeDynamicTrees_of_lengthsOnly hd
            have hple₂ : br₂.pos ≤ br₂.data.size := by
              have := hbp₂; simp only [ZipCommon.BitReader.bitPos] at this; omega
            have hpos₂ : br₂.bitOff = 0 ∨ br₂.pos < br₂.data.size := by
              have := hbp₂; simp only [ZipCommon.BitReader.bitPos] at this
              rcases Nat.lt_or_ge br₂.pos br₂.data.size with h | h
              · exact Or.inr h
              · exact Or.inl (by omega)
            obtain ⟨hd₃, hp₃, hl₃⟩ := Zip.Native.decodeDynamicTrees_inv
              br₂ br₃ _ _ hdyntrees hpos₂ hple₂
            have hbo₃ := InflateBuf.decodeDynamicTrees_bitOff_pres hbo₂ hdyntrees
            have hbp₃ : br₃.bitPos ≤ br₃.data.size * 8 := by
              simp only [ZipCommon.BitReader.bitPos]
              rcases hp₃ with h' | h' <;> omega
            rw [decodeHuffmanCurTablesU_eq br₃ output outPos _ _ _ _ maxOut _
              (treeFree_len_le litLens hlv hlb)
              (fun _ _ _ _ _ _ h => treeFree_decode_used_le litLens hlv hlb h)
              (fun _ _ _ _ _ _ h => treeFree_decode_used_le distLens hdv hdb h)
              hbo₃ hbp₃ hsize]
            cases hb : InflateBuf.decodeHuffmanCurTables br₃ output outPos
                (HuffTree.buildTreeFreeWithCount litLens (HuffTree.countLengthsFast litLens 15) 15).1
                (HuffTree.buildTreeFreeWithCount distLens (HuffTree.countLengthsFast distLens 15) 15).1
                (HuffTree.buildTreeFreeWithCount litLens (HuffTree.countLengthsFast litLens 15) 15).2
                (HuffTree.buildTreeFreeWithCount distLens (HuffTree.countLengthsFast distLens 15) 15).2
                maxOut
                (HuffTree.buildTreeFreeWithCount_size litLens (HuffTree.countLengthsFast litLens 15) 15) with
            | error e => simp only [hb, bind, Except.bind]
            | ok r =>
              obtain ⟨o', p', b'⟩ := r
              simp only [hb, bind, Except.bind]
              exact htail o' p' b' (by rw [decodeHuffmanCurTables_size hb]; exact hsize)
        · rfl

/-- `inflateRawFastU` (branch-free `uset` fastloop) agrees with `inflateRawFast`
    (the `set!` cursor), by `inflateLoopCurU_eq` on the presized buffer. -/
theorem inflateRawFastU_eq (data : ByteArray) (startPos maxOutputSize sizeHint : Nat) :
    Inflate.inflateRawFastU data startPos maxOutputSize sizeHint
      = Inflate.inflateRawFast data startPos maxOutputSize sizeHint := by
  unfold Inflate.inflateRawFastU Inflate.inflateRawFast
  by_cases hg : sizeHint > maxOutputSize
  · simp only [if_pos hg, bind, Except.bind]
  · have hpsz : (ByteArray.presize sizeHint).size = sizeHint := by
      simp only [ByteArray.presize, ByteArray.size, Array.size_replicate]
    simp only [if_neg hg, bind, Except.bind,
      inflateLoopCurU_eq maxOutputSize data.size _ (ByteArray.presize sizeHint) 0
        (by rw [hpsz]; omega)]

/-- **Target (issue #2799): the branch-free `uset` margin-split fastloop decodes
    correctly.** `inflateFastU` on the true decompressed size agrees with the
    reference `Inflate.inflate`, via `inflateRawFastU_eq` (down to `goCurU_eq`)
    composed with the `set!`-cursor correctness `inflateFast_eq`. -/
theorem inflateFastU_eq (data : ByteArray) (maxOut : Nat) (out : ByteArray)
    (hds : data.size < USize.size) (hosz : out.size < USize.size) (hle : out.size ≤ maxOut)
    (href : Inflate.inflate data maxOut = .ok out) :
    Inflate.inflateFastU data maxOut out.size = .ok out := by
  have hf := inflateFast_eq data maxOut out hds hosz hle href
  rw [Inflate.inflateFast] at hf
  rw [Inflate.inflateFastU, inflateRawFastU_eq]
  exact hf

/-- **Production dispatch is correct on valid input.** The exact-size fastloop
    path `inflateSized … (exact := true)` returns exactly `inflate`'s bytes
    whenever the stream is valid: the fast branch is `inflateFastU_eq`, and the
    fallback / empty-output branch is `inflate` itself (the `sizeHint` is inert).
    So promoting the fastloop into a decode path guarded by an exact, bounded
    size never changes the accepted bytes. -/
theorem inflateSized_eq (data : ByteArray) (maxOut : Nat) (out : ByteArray)
    (hds : data.size < USize.size) (hosz : out.size < USize.size) (hle : out.size ≤ maxOut)
    (href : Inflate.inflate data maxOut = .ok out) :
    Inflate.inflateSized data maxOut out.size true = .ok out := by
  rw [Inflate.inflateSized]
  split
  · rw [inflateFastU_eq data maxOut out hds hosz hle href]
  · rw [Inflate.inflate_sizeHint_eq]; exact href

set_option maxHeartbeats 1000000 in
/-- **Soundness — the reverse direction.** Whenever the branch-free `uset` fastloop
    *accepts*, the reference `Inflate.inflate` accepts the same bytes. Chains
    `inflateRawFastU_eq`, the exact-size contract (`cop = cf.size`, and the loop
    preserves size, so `cop = sizeHint`), the reverse loop bisimulation
    `inflateLoopCur_treeFree`, then `inflateRaw_eq_loop`. -/
theorem inflateFastU_sound (data : ByteArray) (maxOut sizeHint : Nat) (o : ByteArray)
    (hds : data.size < USize.size) (hmo : maxOut < USize.size)
    (h : Inflate.inflateFastU data maxOut sizeHint = .ok o) :
    Inflate.inflate data maxOut = .ok o := by
  have hpsz : (ByteArray.presize sizeHint).size = sizeHint := by
    simp only [ByteArray.presize, ByteArray.size, Array.size_replicate]
  have hemp : ByteArray.emptyWithCapacity 0 = (ByteArray.presize sizeHint).extract 0 0 := by
    apply ByteArray.ext_getElem!
    · rw [ByteArray.size_extract]; simp
    · intro i hi; simp at hi
  rw [Inflate.inflateFastU] at h
  obtain ⟨pr, hraw, hret⟩ := bindOk' h
  obtain ⟨o', endPos⟩ := pr
  simp only [pure, Except.pure, Except.ok.injEq] at hret
  rw [inflateRawFastU_eq, Inflate.inflateRawFast] at hraw
  simp only [bind, Except.bind] at hraw
  split at hraw
  · exact absurd hraw (by simp)
  · rename_i hng
    obtain ⟨pl, hloop, hchk⟩ := bindOk' hraw
    obtain ⟨cf, cop, cep⟩ := pl
    simp only [] at hchk
    split at hchk
    · exact absurd hchk (by simp)
    · rename_i hcopeq
      obtain ⟨rfl, rfl⟩ := hchk
      have hcfsz : o'.size = sizeHint := by
        rw [inflateLoopCur_size maxOut data.size _ _ _ _ _ _ hloop, hpsz]
      have hcopval : cop = o'.size := Decidable.of_not_not hcopeq
      have htf := inflateLoopCur_treeFree maxOut data.size hds hmo
        { data := data, pos := 0, bitOff := 0 } (ByteArray.presize sizeHint) 0 o' cop endPos
        (by simp [ZipCommon.BitReader.bitPos]) rfl (by rw [hpsz]; omega) (by rw [hpsz]; omega)
        (by omega) hloop (by rw [hpsz]; omega)
      rw [← hemp] at htf
      have hoext : o'.extract 0 cop = o' := by
        rw [hcopval]
        apply ByteArray.ext_getElem!
        · rw [ByteArray.size_extract]; omega
        · intro i hi
          rw [ByteArray.size_extract] at hi
          rw [ByteArray.getElem!_extract _ 0 _ i (by omega), Nat.zero_add]
      rw [hoext] at htf
      rw [Inflate.inflate]
      simp only [bind, Except.bind]
      rw [Inflate.inflateRaw_eq_loop, htf]
      exact congrArg Except.ok hret

/-- **The `uset` fastloop production dispatch equals the reference decoder,
    unconditionally.** `inflateSized … = inflate`: the fast path returns exactly
    `inflate`'s bytes when it accepts (`inflateFastU_sound`), the fallback and
    inert-hint paths are `inflate` itself. So the fastloop is a true ratchet — no
    CRC backstop is needed for soundness. -/
theorem inflateSized_agrees (data : ByteArray) (maxOut sizeHint : Nat) (exact : Bool)
    (hds : data.size < USize.size) (hmo : maxOut < USize.size) :
    Inflate.inflateSized data maxOut sizeHint exact = Inflate.inflate data maxOut := by
  rw [Inflate.inflateSized]
  split
  · cases hfu : Inflate.inflateFastU data maxOut sizeHint with
    | ok o => exact (inflateFastU_sound data maxOut sizeHint o hds hmo hfu).symm
    | error e => exact Inflate.inflate_sizeHint_eq data maxOut sizeHint
  · exact Inflate.inflate_sizeHint_eq data maxOut sizeHint

set_option maxHeartbeats 1000000 in
/-- **Soundness — the raw-offset reverse direction.** The `inflateRaw` counterpart of
    `inflateFastU_sound`: whenever the branch-free `uset` fastloop *accepts* a stream
    starting at byte offset `startPos`, the reference push decoder `Inflate.inflateRaw`
    accepts the same bytes *and* reports the same byte-aligned end position `ep`.
    Same skeleton as `inflateFastU_sound`, but the loop bisimulation
    `inflateLoopCur_treeFree` is instantiated at `pos := startPos` (needing
    `startPos ≤ data.size`, always true at a gzip member boundary), and the returned
    `endPos` is preserved rather than discarded so a container decoder can locate the
    trailer / next member from it. -/
theorem inflateRawFastU_sound (data : ByteArray) (startPos maxOut sizeHint : Nat)
    (o : ByteArray) (ep : Nat)
    (hds : data.size < USize.size) (hmo : maxOut < USize.size) (hsp : startPos ≤ data.size)
    (h : Inflate.inflateRawFastU data startPos maxOut sizeHint = .ok (o, ep)) :
    Inflate.inflateRaw data startPos maxOut = .ok (o, ep) := by
  have hpsz : (ByteArray.presize sizeHint).size = sizeHint := by
    simp only [ByteArray.presize, ByteArray.size, Array.size_replicate]
  have hemp : ByteArray.emptyWithCapacity 0 = (ByteArray.presize sizeHint).extract 0 0 := by
    apply ByteArray.ext_getElem!
    · rw [ByteArray.size_extract]; simp
    · intro i hi; simp at hi
  rw [inflateRawFastU_eq, Inflate.inflateRawFast] at h
  simp only [bind, Except.bind] at h
  split at h
  · exact absurd h (by simp)
  · rename_i hng
    obtain ⟨pl, hloop, hchk⟩ := bindOk' h
    obtain ⟨cf, cop, cep⟩ := pl
    simp only [] at hchk
    split at hchk
    · exact absurd hchk (by simp)
    · rename_i hcopeq
      obtain ⟨rfl, rfl⟩ := hchk
      have hcfsz : o.size = sizeHint := by
        rw [inflateLoopCur_size maxOut data.size _ _ _ _ _ _ hloop, hpsz]
      have hcopval : cop = o.size := Decidable.of_not_not hcopeq
      have htf := inflateLoopCur_treeFree maxOut data.size hds hmo
        { data := data, pos := startPos, bitOff := 0 } (ByteArray.presize sizeHint) 0 o cop ep
        (by simp only [ZipCommon.BitReader.bitPos]; omega) rfl (by rw [hpsz]; omega)
        (by rw [hpsz]; omega) (by omega) hloop (by rw [hpsz]; omega)
      rw [← hemp] at htf
      have hoext : o.extract 0 cop = o := by
        rw [hcopval]
        apply ByteArray.ext_getElem!
        · rw [ByteArray.size_extract]; omega
        · intro i hi
          rw [ByteArray.size_extract] at hi
          rw [ByteArray.getElem!_extract _ 0 _ i (by omega), Nat.zero_add]
      rw [hoext] at htf
      rw [Inflate.inflateRaw_eq_loop]
      exact htf

/-- **The raw-offset `uset` fastloop dispatch equals the reference decoder.**
    `inflateRawSized … = inflateRaw`: the fast path returns exactly `inflateRaw`'s
    bytes *and* end position when it accepts (`inflateRawFastU_sound`), and the
    fallback / inert-hint branches are `inflateRaw` itself. So wiring the fastloop
    into the gzip member decode never changes the decoded bytes or the member
    boundary; the gzip CRC32 / ISIZE trailer checks stay integrity checks, not
    soundness backstops. -/
theorem inflateRawSized_agrees (data : ByteArray) (startPos maxOut sizeHint : Nat) (exact : Bool)
    (hds : data.size < USize.size) (hmo : maxOut < USize.size) (hsp : startPos ≤ data.size) :
    Inflate.inflateRawSized data startPos maxOut sizeHint exact
      = Inflate.inflateRaw data startPos maxOut := by
  rw [Inflate.inflateRawSized]
  split
  · cases hfu : Inflate.inflateRawFastU data startPos maxOut sizeHint with
    | ok r =>
      obtain ⟨o, ep⟩ := r
      exact (inflateRawFastU_sound data startPos maxOut sizeHint o ep hds hmo hsp hfu).symm
    | error e => rfl
  · rfl

end Zip.Native
