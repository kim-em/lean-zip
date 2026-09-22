import Zip.Native.Parallel
import Zip.Spec.DeflateBlockSplit
import Zip.Spec.InflateTreeFreeCorrect

/-!
# Opt-in multi-threaded DEFLATE — correctness

`deflateDynamicBlocksSCParallel_eq` proves that `Zip/Native/Parallel.lean`'s threaded encoder
is **byte-identical** to `deflateDynamicBlocksSC`, for every flag,
chunk size and level — hence for any number of spawned tasks or cores.  The
four theorems about that encoder are then restated for it by rewriting.

Three facts carry it:

* `task_spawn_get` — a task is its own function call (`Task.spawn f` is `⟨f ()⟩` in
  the logic).  Depends on **no axioms**.
* `appendW_spec` — merging two writers concatenates their bits.  This is what
  makes the *emit* parallelisable, not just the matcher.
* `emitChunkBlock_hom` — the bits a chunk emits do not depend on the writer they
  are emitted onto, because `emitDynBlock_spec` pins them by equations.

## Checking that this adds no axioms

Nothing in Lean diffs an axiom set against a baseline, so the check is
`#print axioms` read in pairs.  Paste into a file after `import Zip` and run it
with `lake env lean`; each new declaration should print the same list as the
existing one below it, or a subset:

    #print axioms task_spawn_get                                  -- no axioms at all
    #print axioms deflateDynamicBlocksSCParallel_eq               -- 43
    #print axioms inflate_deflateDynamicBlocksSC                  -- 45, a superset
    #print axioms inflate_deflateDynamicBlocksSCParallel          -- 45, production decoder
    #print axioms inflate_deflateRaw                              -- 99, a superset
    #print axioms inflateReference_deflateDynamicBlocksSCParallel -- 45
    #print axioms inflate_deflateDynamicBlocksSC                  -- 45, identical
    #print axioms decode_deflateDynamicBlocksSCParallel           -- 43
    #print axioms decode_deflateDynamicBlocksSC                   -- 43, identical

Anything in the first list of a pair that is absent from the second is an axiom
the parallel encoder introduced.  There is none.

None of the entries are FFI axioms — `@[extern]` produces no axioms in Lean, so
the four C primitives never enter the kernel's trusted base.  Every
non-standard entry is a `bv_decide` reflection axiom the library already carries.

## Contents

**The theorem this file turns on is `deflateDynamicBlocksSCParallel_eq`, at
line 295:**

    deflateDynamicBlocksSCParallel data chunkSize level par
      = deflateDynamicBlocksSC data chunkSize level

The threaded encoder and the sequential one produce **the same bytes** — for
every `chunkSize`, every `level` and either setting of `par`, and so for any
number of spawned tasks or cores, since the scheduler never appears in the term
at all.  Everything else in this file is that equality plus one rewrite.

It cannot literally come first: it rests on the merge lemmas, and Lean needs
those declared before they are used.  So, the map.

What it rests on, in the order they appear:

    L161  appendW_spec
             merging two writers concatenates their bits
    L176  task_spawn_get
             a task is its own function call — depends on no axioms
    L180  emitChunkBlock_hom
             a chunk's bits ignore the writer emitted onto
    L211  mergeChunks  (def)
             the sequential merge — the reference the tasks are compared to
    L221  foldl_chunkWriters
             spawning then merging = the sequential merge
    L244  mergeChunks_toBits_eq
             merged bits = the sequential emit's bits

What follows from it — each is `rw [deflateDynamicBlocksSCParallel_eq]` and then
the existing theorem, nothing more:

    L337  inflateReference_deflateDynamicBlocksSCParallel
             the same against the reference decoder
    L349  inflate_deflateDynamicBlocksSCParallel
             Inflate.inflate (threaded output) = .ok data — the PRODUCTION decoder
    L358  decode_deflateDynamicBlocksSCParallel
             the spec decoder reproduces the input
    L367  deflateDynamicBlocksSCParallel_goR_pad
             format: stream consumed, <8 bits padding
    L377  deflateDynamicBlocksSCParallel_pad
             format: content bits + <8 bits padding

Supporting `BitWriter` lemmas behind `appendW_spec`: `writeBitsLSB_eq`,
`byteToBits_eq`, `appendBytesFrom_spec`, `appendPending_spec`.

-/

namespace Zip.Native.BitWriter
open Deflate.Spec

theorem writeBitsLSB_eq (n v : Nat) :
    writeBitsLSB n v = (List.range n).map (fun i => v.testBit i) := by
  induction n generalizing v with
  | zero => rfl
  | succ n ih =>
    rw [writeBitsLSB, ih, List.range_succ_eq_map, List.map_cons, List.map_map]
    congr 1
    · simp [Nat.testBit_zero]; rfl
    · apply List.map_congr_left; intro i _; simp [Function.comp, Nat.testBit_succ]

theorem byteToBits_eq (b : UInt8) :
    bytesToBits.byteToBits b = writeBitsLSB 8 b.toNat := by
  rw [writeBitsLSB_eq]
  apply List.ext_getElem
  · simp [bytesToBits.byteToBits]
  · intro i h1 h2
    simp only [bytesToBits.byteToBits, List.length_ofFn] at h1
    rcases i with _|_|_|_|_|_|_|_|i <;>
      simp_all [bytesToBits.byteToBits, Nat.testBit_zero] <;> omega

theorem appendBytesFrom_spec (a : BitWriter) (b : ByteArray) (i : Nat) :
    a.wf → (appendBytesFrom a b i).toBits
        = a.toBits ++ (b.data.toList.drop i).flatMap bytesToBits.byteToBits
      ∧ (appendBytesFrom a b i).wf := by
  fun_induction appendBytesFrom a b i with
  | case1 a i h ih =>
    intro ha
    obtain ⟨h1, h2⟩ := ih (writeBits_wf a 8 _ ha (by omega))
    refine ⟨?_, h2⟩
    rw [h1, writeBits_toBits a 8 _ ha (by omega)]
    have hb : (b[i].toUInt32).toNat = b[i].toNat := by simp
    rw [hb, ← byteToBits_eq]
    have hlt : i < b.data.toList.length := by simpa using h
    rw [List.drop_eq_getElem_cons hlt]
    simp
    rfl
  | case2 a i h =>
    intro ha
    have : b.data.toList.drop i = [] := by
      apply List.drop_eq_nil_of_le; simpa using Nat.le_of_not_lt h
    simp [this, ha]

theorem appendPending_spec (a : BitWriter) (buf : UInt64) (n i : Nat) :
    a.wf → (appendPending a buf n i).toBits
        = a.toBits ++ ((List.range n).drop i).map (fun k => buf.toNat.testBit k)
      ∧ (appendPending a buf n i).wf := by
  fun_induction appendPending a buf n i with
  | case1 a i h ih =>
    intro ha
    obtain ⟨h1, h2⟩ := ih (writeBits_wf a 1 _ ha (by omega))
    refine ⟨?_, h2⟩
    rw [h1, writeBits_toBits a 1 _ ha (by omega)]
    have hlt : i < (List.range n).length := by simpa using h
    rw [List.drop_eq_getElem_cons hlt]
    cases hbit : buf.toNat.testBit i <;> simp [writeBitsLSB, hbit]
  | case2 a i h =>
    intro ha
    have : (List.range n).drop i = [] := by
      apply List.drop_eq_nil_of_le; simpa using Nat.le_of_not_lt h
    simp [this, ha]

/-- **Bit-level concatenation**: appending `b` onto `a` appends exactly `b`'s bits. -/
theorem appendW_spec (a b : BitWriter) (ha : a.wf) :
    (appendW a b).toBits = a.toBits ++ b.toBits ∧ (appendW a b).wf := by
  obtain ⟨h1, h2⟩ := appendBytesFrom_spec a b.data 0 ha
  obtain ⟨h3, h4⟩ := appendPending_spec _ b.bitBuf b.bitCount.toNat 0 h2
  refine ⟨?_, h4⟩
  rw [appendW, h3, h1, List.append_assoc]
  rfl

end Zip.Native.BitWriter

namespace Zip.Native.Deflate
open Deflate.Spec Zip.Native.BitWriter

/-- A spawned task's value is its function applied: in the logic `Task.spawn f`
    is `⟨f ()⟩`, so threading is computationally inert.  Depends on no axioms. -/
theorem task_spawn_get {α : Type} (f : Unit → α) : (Task.spawn f).get = f () := rfl

/-- The bits a chunk's block emits do not depend on the writer it is emitted
    onto: `emitDynBlock_spec` pins them by equations on the chunk's tokens. -/
theorem emitChunkBlock_hom (data : ByteArray) (pos j : Nat) (level : UInt8)
    (bw : BitWriter) (hbw : bw.wf) (isFinal : Bool) :
    (emitChunkBlock bw data pos j level isFinal).toBits
      = bw.toBits ++ (chunkFrag data level pos j isFinal).toBits := by
  obtain ⟨l1, d1, h1, s1, hll1, hdl1, _, _, _, _, _, _, _, _, htrees1, hsyms1, htoBits1, _⟩ :=
    emitDynBlock_spec bw hbw (data.extract pos j) (lzMatch (data.extract pos j) level)
      (lzMatch_encodable (data.extract pos j) level)
      (fun hz => lzMatch_empty (data.extract pos j) level hz) isFinal
  obtain ⟨l2, d2, h2, s2, hll2, hdl2, _, _, _, _, _, _, _, _, htrees2, hsyms2, htoBits2, _⟩ :=
    emitDynBlock_spec BitWriter.empty BitWriter.empty_wf (data.extract pos j)
      (lzMatch (data.extract pos j) level)
      (lzMatch_encodable (data.extract pos j) level)
      (fun hz => lzMatch_empty (data.extract pos j) level hz) isFinal
  have hl : l1 = l2 := by rw [hll1, hll2]
  have hd : d1 = d2 := by rw [hdl1, hdl2]
  subst hl; subst hd
  have hh : h1 = h2 := by
    have := htrees1.symm.trans htrees2
    exact Option.some.inj this
  have hs : s1 = s2 := by
    have := hsyms1.symm.trans hsyms2
    exact Option.some.inj this
  subst hh; subst hs
  simp only [emitChunkBlock, chunkFrag] at *
  rw [htoBits1, htoBits2, BitWriter.empty_toBits, List.nil_append]
  simp [List.append_assoc]

/-- The sequential reference for the parallel path: merge the per-chunk writers
    left to right.  Nothing at runtime calls this; `foldl_chunkWriters` shows the
    spawned-then-merged tasks equal it, and `mergeChunks_toBits_eq` shows its bits
    equal `emitChunkBlocks`'s. -/
def mergeChunks (data : ByteArray) (chunkSize : Nat) (level : UInt8) (pos : Nat)
    (bw : BitWriter) : BitWriter :=
  let j := min (pos + max chunkSize 1) data.size
  let bw := appendW bw (chunkFrag data level pos j (decide (j ≥ data.size)))
  if j ≥ data.size then bw
  else mergeChunks data chunkSize level j bw
termination_by data.size - pos
decreasing_by simp_all only [Nat.not_le]; omega

/-- Merging the spawned writers left to right is the sequential merge. -/
theorem foldl_chunkWriters (data : ByteArray) (chunkSize : Nat) (level : UInt8) :
    ∀ (pos : Nat) (bw : BitWriter), pos < data.size →
      (chunkWriters data chunkSize level pos).foldl (fun w t => appendW w t.get) bw
        = mergeChunks data chunkSize level pos bw := by
  intro pos bw
  fun_induction mergeChunks data chunkSize level pos bw with
  | case1 p b j bw2 hend =>
    intro hp
    rw [chunkWriters]
    simp only [ge_iff_le, Nat.not_le.mpr hp, ite_false]
    rw [List.foldl_cons, task_spawn_get, chunkWriters]
    have hend' : min (p + max chunkSize 1) data.size ≥ data.size := hend
    rw [ite_eq_left hend']
    rfl
  | case2 p b j bw2 hend ih =>
    intro hp
    rw [chunkWriters]
    simp only [ge_iff_le, Nat.not_le.mpr hp, ite_false]
    rw [List.foldl_cons, task_spawn_get]
    exact ih (by omega)

/-- The parallel merge and the sequential `emitChunkBlocks` produce the same bits,
    starting from any two writers that already hold the same bits. -/
theorem mergeChunks_toBits_eq (data : ByteArray) (chunkSize : Nat) (level : UInt8) :
    ∀ (fuel pos : Nat) (a b : BitWriter), data.size - pos ≤ fuel → pos < data.size →
      a.wf → b.wf → a.toBits = b.toBits →
      (mergeChunks data chunkSize level pos a).toBits
          = (emitChunkBlocks data chunkSize level pos b).toBits
        ∧ (mergeChunks data chunkSize level pos a).wf := by
  intro fuel
  induction fuel with
  | zero => intro pos a b hf hpos _ _ _; omega
  | succ fuel ih =>
    intro pos a b hf hpos ha hb hab
    have hjle : min (pos + max chunkSize 1) data.size ≤ data.size := Nat.min_le_right _ _
    have hjgt : pos < min (pos + max chunkSize 1) data.size := by simp only [Nat.lt_min]; omega
    obtain ⟨_, _, hwfB, _, _⟩ :=
      emitChunkBlock_decode data pos (min (pos + max chunkSize 1) data.size) level b hb (decide (min (pos + max chunkSize 1) data.size ≥ data.size))
    have hhom := emitChunkBlock_hom data pos (min (pos + max chunkSize 1) data.size) level b hb (decide (min (pos + max chunkSize 1) data.size ≥ data.size))
    obtain ⟨happ, hwfapp⟩ :=
      appendW_spec a (chunkFrag data level pos (min (pos + max chunkSize 1) data.size) (decide (min (pos + max chunkSize 1) data.size ≥ data.size))) ha
    have hbits : (appendW a (chunkFrag data level pos (min (pos + max chunkSize 1) data.size) (decide (min (pos + max chunkSize 1) data.size ≥ data.size)))).toBits
        = (emitChunkBlock b data pos (min (pos + max chunkSize 1) data.size) level (decide (min (pos + max chunkSize 1) data.size ≥ data.size))).toBits := by
      rw [happ, hhom, hab]
    by_cases hend : min (pos + max chunkSize 1) data.size ≥ data.size
    · have hstepM : mergeChunks data chunkSize level pos a
          = appendW a (chunkFrag data level pos (min (pos + max chunkSize 1) data.size) (decide (min (pos + max chunkSize 1) data.size ≥ data.size))) := by
        conv => lhs; unfold mergeChunks
        simp only [ite_eq_left hend]
      have hstepE : emitChunkBlocks data chunkSize level pos b
          = emitChunkBlock b data pos (min (pos + max chunkSize 1) data.size) level (decide (min (pos + max chunkSize 1) data.size ≥ data.size)) := by
        conv => lhs; unfold emitChunkBlocks
        simp only [ite_eq_left hend]
      rw [hstepM, hstepE]
      exact ⟨hbits, hwfapp⟩
    · have hstepM : mergeChunks data chunkSize level pos a
          = mergeChunks data chunkSize level (min (pos + max chunkSize 1) data.size)
            (appendW a (chunkFrag data level pos (min (pos + max chunkSize 1) data.size) (decide (min (pos + max chunkSize 1) data.size ≥ data.size)))) := by
        conv => lhs; unfold mergeChunks
        simp only [ite_eq_right hend]
      have hstepE : emitChunkBlocks data chunkSize level pos b
          = emitChunkBlocks data chunkSize level (min (pos + max chunkSize 1) data.size)
            (emitChunkBlock b data pos (min (pos + max chunkSize 1) data.size) level (decide (min (pos + max chunkSize 1) data.size ≥ data.size))) := by
        conv => lhs; unfold emitChunkBlocks
        simp only [ite_eq_right hend]
      rw [hstepM, hstepE]
      exact ih (min (pos + max chunkSize 1) data.size) _ _ (by omega) (by omega) hwfapp hwfB hbits

/-- **Threading and chunk-parallel emission cannot change the output**: the
    result is byte-identical to `deflateDynamicBlocksSC` for every flag, chunk size and level,
    hence for any number of spawned tasks or cores.

    Everything from here to the end of the file is this equality plus one
    `rw`, in the order the header's contents map lists them. -/
theorem deflateDynamicBlocksSCParallel_eq (data : ByteArray) (chunkSize : Nat) (level : UInt8) (par : Bool) :
    deflateDynamicBlocksSCParallel data chunkSize level par = deflateDynamicBlocksSC data chunkSize level := by
  rw [deflateDynamicBlocksSCParallel]
  split
  · split
    · rfl
    · rename_i hz
      have hpos : 0 < data.size := by
        rcases Nat.eq_zero_or_pos data.size with h | h
        · rw [h] at hz; simp at hz
        · exact h
      rw [foldl_chunkWriters data chunkSize level 0 BitWriter.empty hpos]
      obtain ⟨heq, hwfm⟩ := mergeChunks_toBits_eq data chunkSize level data.size 0
        BitWriter.empty BitWriter.empty (by omega) hpos
        BitWriter.empty_wf BitWriter.empty_wf rfl
      obtain ⟨_, _, hwfE, _⟩ := emitChunkBlocks_decode data chunkSize level data.size 0
        BitWriter.empty (by omega) hpos BitWriter.empty_wf
      conv => rhs; rw [deflateDynamicBlocksSC]
      rw [ite_eq_right hz]
      exact flush_eq_of_toBits _ _ hwfm hwfE heq
  · rfl

/-! ## The four `deflateDynamicBlocksSC` theorems, restated

Nothing below proves anything new about the DEFLATE format.  The threaded
encoder emits the *same bytes* as the sequential one
(`deflateDynamicBlocksSCParallel_eq`), so each of these is the corresponding
existing theorem plus a single rewrite:

    rw [deflateDynamicBlocksSCParallel_eq]   -- the two encoders agree, byte for byte
    exact <the existing theorem>             -- which already covers those bytes

The one most callers will want is `inflate_deflateDynamicBlocksSCParallel`:
inflating what the threaded encoder produced, **with the production decoder the
library ships**, returns `.ok data` — for every chunk size, every level and
either setting of `par`. -/

/-- **Round trip, reference decoder.**  Inflating the threaded encoder's output
    returns `.ok data`, for every `chunkSize`, every `level` and either setting of
    `par` — and hence for any number of spawned tasks or cores.  Named after
    `inflateReference_deflateRaw`: this is the *reference* decoder.
    The production statement is `inflate_deflateDynamicBlocksSCParallel` below. -/
theorem inflateReference_deflateDynamicBlocksSCParallel (data : ByteArray) (chunkSize : Nat)
    (level : UInt8) (par : Bool) (maxOutputSize : Nat) (hsize : data.size ≤ maxOutputSize) :
    Zip.Native.Inflate.inflateReference (deflateDynamicBlocksSCParallel data chunkSize level par)
      maxOutputSize = .ok data := by
  rw [deflateDynamicBlocksSCParallel_eq]
  exact inflate_deflateDynamicBlocksSC data chunkSize level maxOutputSize hsize

/-- **Round trip, production decoder.**  The same statement against
    `Inflate.inflate`, the tree-free decoder the library actually ships — the one
    the headline `zlib_decompressSingle_compress` runs through.  Bridged by
    `Inflate.inflate_ok_iff_reference`, exactly as `inflate_deflateRaw`
    is derived from `inflateReference_deflateRaw`. -/
theorem inflate_deflateDynamicBlocksSCParallel (data : ByteArray) (chunkSize : Nat)
    (level : UInt8) (par : Bool) (maxOutputSize : Nat) (hsize : data.size ≤ maxOutputSize) :
    Zip.Native.Inflate.inflate (deflateDynamicBlocksSCParallel data chunkSize level par)
      maxOutputSize = .ok data :=
  (Zip.Native.Inflate.inflate_ok_iff_reference _ _ _).mpr
    (inflateReference_deflateDynamicBlocksSCParallel data chunkSize level par maxOutputSize hsize)

/-- The spec decoder reproduces the input from the threaded encoder's bits, for
    every `chunkSize`, every `level` and either setting of `par`. -/
theorem decode_deflateDynamicBlocksSCParallel (data : ByteArray) (chunkSize : Nat)
    (level : UInt8) (par : Bool) :
    decode (bytesToBits (deflateDynamicBlocksSCParallel data chunkSize level par))
      = some data.data.toList := by
  rw [deflateDynamicBlocksSCParallel_eq]
  exact decode_deflateDynamicBlocksSC data chunkSize level

/-- Format: the decoder consumes the stream, leaving under a byte of padding —
    for every `chunkSize`, every `level` and either setting of `par`. -/
theorem deflateDynamicBlocksSCParallel_goR_pad (data : ByteArray) (chunkSize : Nat)
    (level : UInt8) (par : Bool) :
    ∃ remaining,
      decode.goR (bytesToBits (deflateDynamicBlocksSCParallel data chunkSize level par)) []
        = some (data.data.toList, remaining) ∧ remaining.length < 8 := by
  rw [deflateDynamicBlocksSCParallel_eq]
  exact deflateDynamicBlocksSC_goR_pad data chunkSize level

/-- Format: the output is content bits plus under a byte of padding, for every
    `chunkSize`, every `level` and either setting of `par`. -/
theorem deflateDynamicBlocksSCParallel_pad (data : ByteArray) (chunkSize : Nat)
    (level : UInt8) (par : Bool) :
    ∃ (contentBits padding : List Bool),
      bytesToBits (deflateDynamicBlocksSCParallel data chunkSize level par)
        = contentBits ++ padding ∧ padding.length < 8 := by
  rw [deflateDynamicBlocksSCParallel_eq]
  exact deflateDynamicBlocksSC_pad data chunkSize level

end Zip.Native.Deflate
