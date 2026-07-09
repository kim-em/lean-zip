import Zip.Native.InflateFast
import Zip.Spec.InflateTreeFreeCorrect
import Zip.Spec.DecodeCorrect

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
* `copyWithinAt` at the cursor, then extract, equals `copyLoop` on the logical
  prefix (a back-reference) — `copyWithinAt_extract_eq_copyLoop` below.

Both need a **big-enough buffer** (`buf.size ≥ final reference size`), which is
carried through the induction and discharged at each step by the reference's
monotone output growth (`goTreeFree_size_mono`).

Status: **work in progress** (issue #2799). Both write bridges
(`set!_extract_eq_push`, `copyWithinAt_extract_eq_copyLoop`) and the reference
monotonicity lemma (`goTreeFree_size_mono`) are proved, with all their
supporting `copyWithinAtGo` content lemmas and `getElem!` infrastructure. The
remaining `sorry` is the top-level target `inflateFast_eq`, which needs the
`goCur` bisimulation (a 10-case induction threading the output invariant and
applying the two write bridges at the write steps) and the block-loop lift. This
file is standalone — not imported by `Zip` — so `Inflate.inflate` and CI stay
`sorry`-free.
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

open InflateBuf (goCur goTreeFreeU)

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

/-- **Target (issue #2799): the write-once cursor decoder agrees with the verified
    decoder on the exact-size path.** Proof staged: `goCur_eq` bisimulation, the
    `goCurU` reduction, and the block-loop lift. -/
theorem inflateFast_eq (data : ByteArray) (maxOut : Nat) (out : ByteArray)
    (href : Inflate.inflate data maxOut = .ok out) :
    Inflate.inflateFast data maxOut out.size = .ok out := by
  sorry

end Zip.Native
