import Zip.Native.Deflate
import Zip.Spec.EmitTokensCorrect
import Zip.Spec.HuffmanEncode

/-!
  Token-stream frequency analysis and dynamic-Huffman code-length selection,
  shared by the dynamic-block emitters (`Zip.Native.DeflateDynamic`) and the
  near-optimal parser's cost model (`Zip.Native.DeflateParse`). Factored out
  of `DeflateDynamic` so the parser, which feeds the emitters, can sit below
  them in the import order.
-/

namespace Zip.Native.Deflate

/-- Count symbol frequencies from LZ77 tokens.
    Returns `(litLenFreqs, distFreqs)` where:
    - `litLenFreqs` has 286 entries (symbols 0–285)
    - `distFreqs` has 30 entries (distance codes 0–29)
    Always includes end-of-block (symbol 256) with frequency 1. -/
def tokenFreqs (tokens : Array LZ77Token) : Array Nat × Array Nat :=
  let litLenFreqs := Array.replicate 286 0
  let distFreqs := Array.replicate 30 0
  -- Always count end-of-block
  let litLenFreqs := litLenFreqs.set! 256 1
  go tokens litLenFreqs distFreqs
    (by show ((Array.replicate 286 0).set! 256 1).size = 286
        rw [Array.size_set!, Array.size_replicate])
    (by show (Array.replicate 30 0).size = 30
        rw [Array.size_replicate]) 0
where
  go (tokens : Array LZ77Token) (litLenFreqs distFreqs : Array Nat)
      (hlit : litLenFreqs.size = 286) (hdist : distFreqs.size = 30)
      (i : Nat) : Array Nat × Array Nat :=
    if h : i < tokens.size then
      match tokens[i] with
      | .literal b =>
        let idx := b.toNat
        have hidx : idx < litLenFreqs.size := by
          have := UInt8.toNat_lt b; omega
        let litLenFreqs' := litLenFreqs.set! idx (litLenFreqs[idx] + 1)
        go tokens litLenFreqs' distFreqs
          (by simp [litLenFreqs', hlit]) hdist (i + 1)
      | .reference length distance =>
        match hflc : findLengthCode length with
        | none =>
          match hfdc : findDistCode distance with
          | none => go tokens litLenFreqs distFreqs hlit hdist (i + 1)
          | some (dIdx, _, _) =>
            have hd : dIdx < distFreqs.size := by
              have := nativeFindDistCode_idx_bound _ _ _ _ hfdc; omega
            let distFreqs' := distFreqs.set! dIdx (distFreqs[dIdx] + 1)
            go tokens litLenFreqs distFreqs' hlit
              (by show (distFreqs.set! dIdx (distFreqs[dIdx] + 1)).size = 30
                  rw [Array.size_set!]; exact hdist)
              (i + 1)
        | some (lIdx, _, _) =>
          have hsym : lIdx + 257 < litLenFreqs.size := by
            have := nativeFindLengthCode_idx_bound _ _ _ _ hflc; omega
          let litLenFreqs' := litLenFreqs.set! (lIdx + 257) (litLenFreqs[lIdx + 257] + 1)
          have hlit' : litLenFreqs'.size = 286 := by
            show (litLenFreqs.set! (lIdx + 257) (litLenFreqs[lIdx + 257] + 1)).size = 286
            rw [Array.size_set!]; exact hlit
          match hfdc : findDistCode distance with
          | none => go tokens litLenFreqs' distFreqs hlit' hdist (i + 1)
          | some (dIdx, _, _) =>
            have hd : dIdx < distFreqs.size := by
              have := nativeFindDistCode_idx_bound _ _ _ _ hfdc; omega
            let distFreqs' := distFreqs.set! dIdx (distFreqs[dIdx] + 1)
            go tokens litLenFreqs' distFreqs' hlit'
              (by show (distFreqs.set! dIdx (distFreqs[dIdx] + 1)).size = 30
                  rw [Array.size_set!]; exact hdist)
              (i + 1)
    else (litLenFreqs, distFreqs)
  termination_by tokens.size - i

/-! ## Packed-token frequency pass (Wave 3b stage B)

`tokenFreqsP` computes the same histogram as `tokenFreqs` directly from the
`packTok`-encoded `UInt32` stream (`lzMatchP`), so the frequency pass never
materializes boxed `LZ77Token`s. The per-token work lives in three
non-recursive helpers (`bumpLitFreqP`/`bumpRefLitFreqP`/`bumpRefDistFreqP`)
whose tag-bit test and field reads are the *exact* bit expressions of
`unpackTok`; the loop body then contains only plain helper applications.
That shape is load-bearing twice over:

* **Correctness**: each helper step is literally the matching `tokenFreqs.go`
  arm over `unpackTok w`, so `tokenFreqsP ws = tokenFreqs (ws.map unpackTok)`
  holds for **every** word array (`tokenFreqsP_eq`) — no encodability side
  condition and no array-content invariants.
* **Elaboration**: the well-founded-recursion translation compares the loop
  body against itself at full transparency, and any match scrutinee or
  projection over a `>>>`-of-a-stuck-word expression sends that `whnf` into
  `findTableCode`'s `WellFounded.Nat.fix` fuel, which does not terminate in
  practical time (deterministic-timeout). Keeping every match *inside* the
  opaque helper constants and every size invariant in a `Subtype`-wrapped
  array parameter (erased at runtime — a trivial structure) keeps the loop
  body free of forced reductions. Do not inline the helpers back into `go`.
-/

/-- Bump the literal/length histogram for one packed literal token
    (tag bit clear): increment index `w.toUInt8.toNat`, exactly
    `tokenFreqs.go`'s literal arm over `unpackTok w`. -/
@[inline] def bumpLitFreqP (litLenFreqs : {a : Array Nat // a.size = 286}) (w : UInt32) :
    {a : Array Nat // a.size = 286} :=
  let idx := w.toUInt8.toNat
  have hidx : idx < litLenFreqs.val.size := by
    have := UInt8.toNat_lt w.toUInt8; have := litLenFreqs.property; omega
  ⟨litLenFreqs.val.set! idx (litLenFreqs.val[idx] + 1),
    by rw [Array.size_set!]; exact litLenFreqs.property⟩

/-- Bump the literal/length histogram for one packed reference token:
    decode the length field with `unpackTok`'s bit expression and count its
    length code, exactly `tokenFreqs.go`'s reference arm (lit/len half). -/
@[inline] def bumpRefLitFreqP (litLenFreqs : {a : Array Nat // a.size = 286}) (w : UInt32) :
    {a : Array Nat // a.size = 286} :=
  match hflc : findLengthCodeFast (((w >>> 16) &&& 0x7FFF).toNat) with
  | none => litLenFreqs
  | some (lIdx, _, _) =>
    have hsym : lIdx + 257 < litLenFreqs.val.size := by
      have := nativeFindLengthCode_idx_bound _ _ _ _
        ((findLengthCodeFast_eq _).symm.trans hflc)
      have := litLenFreqs.property; omega
    ⟨litLenFreqs.val.set! (lIdx + 257) (litLenFreqs.val[lIdx + 257] + 1),
      by rw [Array.size_set!]; exact litLenFreqs.property⟩

/-- Bump the distance histogram for one packed reference token: decode the
    distance field with `unpackTok`'s bit expression and count its distance
    code, exactly `tokenFreqs.go`'s reference arm (distance half). -/
@[inline] def bumpRefDistFreqP (distFreqs : {a : Array Nat // a.size = 30}) (w : UInt32) :
    {a : Array Nat // a.size = 30} :=
  match hfdc : findDistCodeFast ((w &&& 0xFFFF).toNat) with
  | none => distFreqs
  | some (dIdx, _, _) =>
    have hd : dIdx < distFreqs.val.size := by
      have := nativeFindDistCode_idx_bound _ _ _ _
        ((findDistCodeFast_eq _).symm.trans hfdc)
      have := distFreqs.property; omega
    ⟨distFreqs.val.set! dIdx (distFreqs.val[dIdx] + 1),
      by rw [Array.size_set!]; exact distFreqs.property⟩

/-- Packed-token form of `tokenFreqs`: the same histogram (286 lit/len
    entries, 30 distance entries, end-of-block pre-counted) computed from the
    packed `UInt32` stream. Equal to `tokenFreqs` over the boxed view for
    every word array (`tokenFreqsP_eq`). -/
def tokenFreqsP (tokens : Array UInt32) : Array Nat × Array Nat :=
  go tokens ⟨(Array.replicate 286 0).set! 256 1,
      by rw [Array.size_set!, Array.size_replicate]⟩
    ⟨Array.replicate 30 0, by rw [Array.size_replicate]⟩ 0
where
  go (tokens : Array UInt32) (litLenFreqs : {a : Array Nat // a.size = 286})
      (distFreqs : {a : Array Nat // a.size = 30}) (i : Nat) : Array Nat × Array Nat :=
    if h : i < tokens.size then
      let w := tokens[i]
      if w &&& ((1 : UInt32) <<< 31) = 0 then
        go tokens (bumpLitFreqP litLenFreqs w) distFreqs (i + 1)
      else
        go tokens (bumpRefLitFreqP litLenFreqs w) (bumpRefDistFreqP distFreqs w) (i + 1)
    else (litLenFreqs.val, distFreqs.val)
  termination_by tokens.size - i

/-- `bumpRefLitFreqP` when the length field has no length code: no-op. -/
private theorem bumpRefLitFreqP_none (lf : {a : Array Nat // a.size = 286}) (w : UInt32)
    (h : findLengthCode (((w >>> 16) &&& 0x7FFF).toNat) = none) :
    bumpRefLitFreqP lf w = lf := by
  unfold bumpRefLitFreqP
  split
  · rfl
  · rename_i heq
    rw [findLengthCodeFast_eq, h] at heq
    cases heq

/-- `bumpRefLitFreqP` when the length field finds code `lIdx`: bump symbol
    `lIdx + 257`. -/
private theorem bumpRefLitFreqP_some (lf : {a : Array Nat // a.size = 286}) (w : UInt32)
    (lIdx en : Nat) (ev : UInt32)
    (h : findLengthCode (((w >>> 16) &&& 0x7FFF).toNat) = some (lIdx, en, ev)) :
    bumpRefLitFreqP lf w =
      ⟨lf.val.set! (lIdx + 257) (lf.val[lIdx + 257]'(by
          have := nativeFindLengthCode_idx_bound _ _ _ _ h
          have := lf.property; omega) + 1),
        by rw [Array.size_set!]; exact lf.property⟩ := by
  unfold bumpRefLitFreqP
  split
  · rename_i heq
    rw [findLengthCodeFast_eq, h] at heq
    cases heq
  · rename_i lIdx' en' ev' heq
    rw [findLengthCodeFast_eq, h] at heq
    simp only [Option.some.injEq, Prod.mk.injEq] at heq
    obtain ⟨rfl, rfl, rfl⟩ := heq
    rfl

/-- `bumpRefDistFreqP` when the distance field has no distance code: no-op. -/
private theorem bumpRefDistFreqP_none (df : {a : Array Nat // a.size = 30}) (w : UInt32)
    (h : findDistCode ((w &&& 0xFFFF).toNat) = none) :
    bumpRefDistFreqP df w = df := by
  unfold bumpRefDistFreqP
  split
  · rfl
  · rename_i heq
    rw [findDistCodeFast_eq, h] at heq
    cases heq

/-- `bumpRefDistFreqP` when the distance field finds code `dIdx`: bump it. -/
private theorem bumpRefDistFreqP_some (df : {a : Array Nat // a.size = 30}) (w : UInt32)
    (dIdx en : Nat) (ev : UInt32)
    (h : findDistCode ((w &&& 0xFFFF).toNat) = some (dIdx, en, ev)) :
    bumpRefDistFreqP df w =
      ⟨df.val.set! dIdx (df.val[dIdx]'(by
          have := nativeFindDistCode_idx_bound _ _ _ _ h
          have := df.property; omega) + 1),
        by rw [Array.size_set!]; exact df.property⟩ := by
  unfold bumpRefDistFreqP
  split
  · rename_i heq
    rw [findDistCodeFast_eq, h] at heq
    cases heq
  · rename_i dIdx' en' ev' heq
    rw [findDistCodeFast_eq, h] at heq
    simp only [Option.some.injEq, Prod.mk.injEq] at heq
    obtain ⟨rfl, rfl, rfl⟩ := heq
    rfl

/-- The packed histogram loop is the boxed one over the `unpackTok` view:
    lockstep induction. Per word, the tag-bit test reduces both sides into
    the same branch; the literal arms agree definitionally, and the
    reference arms agree by splitting the boxed side's `findLengthCode` /
    `findDistCode` matches and rewriting the packed helpers with the
    resulting equations (`bumpRef*FreqP_none`/`_some`). -/
private theorem tokenFreqsP_go_eq (ws : Array UInt32) (litF distF : Array Nat)
    (hlit : litF.size = 286) (hdist : distF.size = 30) (i : Nat) :
    tokenFreqsP.go ws ⟨litF, hlit⟩ ⟨distF, hdist⟩ i =
      tokenFreqs.go (ws.map unpackTok) litF distF hlit hdist i := by
  induction h : ws.size - i using Nat.strongRecOn generalizing litF distF hlit hdist i with
  | _ n ih =>
    unfold tokenFreqsP.go tokenFreqs.go
    by_cases hi : i < ws.size
    · simp only [Array.size_map, hi, ↓reduceDIte, Array.getElem_map, unpackTok]
      by_cases hc : ws[i] &&& ((1 : UInt32) <<< 31) = 0
      · simp only [hc, ↓reduceIte, bumpLitFreqP]
        exact ih (ws.size - (i + 1)) (by omega) _ _ _ _ _ rfl
      · simp only [hc, ↓reduceIte]
        split
        · rename_i hflc
          split
          · rename_i hfdc
            rw [bumpRefLitFreqP_none _ _ hflc, bumpRefDistFreqP_none _ _ hfdc]
            exact ih (ws.size - (i + 1)) (by omega) _ _ _ _ _ rfl
          · rename_i dIdx en ev hfdc
            rw [bumpRefLitFreqP_none _ _ hflc, bumpRefDistFreqP_some _ _ _ _ _ hfdc]
            exact ih (ws.size - (i + 1)) (by omega) _ _ _ _ _ rfl
        · rename_i lIdx en ev hflc
          split
          · rename_i hfdc
            rw [bumpRefLitFreqP_some _ _ _ _ _ hflc, bumpRefDistFreqP_none _ _ hfdc]
            exact ih (ws.size - (i + 1)) (by omega) _ _ _ _ _ rfl
          · rename_i dIdx en' ev' hfdc
            rw [bumpRefLitFreqP_some _ _ _ _ _ hflc, bumpRefDistFreqP_some _ _ _ _ _ hfdc]
            exact ih (ws.size - (i + 1)) (by omega) _ _ _ _ _ rfl
    · simp only [Array.size_map, hi, ↓reduceDIte]

/-- `tokenFreqsP` is `tokenFreqs` over the boxed view of the words —
    unconditionally, for every word array. Producers whose boxed view is a
    boxed token stream (e.g. `lzMatchP` via `lzMatchP_map`) inherit
    `tokenFreqsP packed = tokenFreqs boxed` by rewriting the view. -/
theorem tokenFreqsP_eq (ws : Array UInt32) :
    tokenFreqsP ws = tokenFreqs (ws.map unpackTok) := by
  unfold tokenFreqsP tokenFreqs
  exact tokenFreqsP_go_eq ws _ _ _ _ 0

/-- Build the `(symbol, freq)` pair list for a frequency array. -/
def freqsToPairs (freqs : Array Nat) : List (Nat × Nat) :=
  (List.range freqs.size).pmap
    (fun i (h : i < freqs.size) => (i, freqs[i]'h))
    (fun _ hi => List.mem_range.mp hi)

/-- The dynamic-Huffman code lengths chosen for the tokens summarised by
    `(litFreqs, distFreqs)`: `computeCodeLengths` over each alphabet, with the
    RFC 1951 fixup that forces at least one non-zero distance code. Shared by the
    block emitter (`deflateDynamicBlock`) and the size-then-emit dispatch so both
    select identical trees from a single computation. -/
def dynamicCodeLengths (litFreqs distFreqs : Array Nat) : List Nat × List Nat :=
  let litLens := Huffman.Spec.computeCodeLengths (freqsToPairs litFreqs) 286 15
  let distLens := Huffman.Spec.computeCodeLengths (freqsToPairs distFreqs) 30 15
  let distLens := if distLens.all (· == 0) then distLens.set 0 1 else distLens
  (litLens, distLens)

/-- The dynamic-Huffman code lengths chosen for the tokens summarised by
    `(litFreqs, distFreqs)` have the standard lengths: 286 lit/len, 30 distance. -/
theorem dynamicCodeLengths_length (litFreqs distFreqs : Array Nat) :
    (dynamicCodeLengths litFreqs distFreqs).1.length = 286 ∧
    (dynamicCodeLengths litFreqs distFreqs).2.length = 30 := by
  refine ⟨Huffman.Spec.computeCodeLengths_length _ 286 15, ?_⟩
  show List.length (if _ then _ else _) = 30
  split
  · rw [List.length_set]; exact Huffman.Spec.computeCodeLengths_length _ 30 15
  · exact Huffman.Spec.computeCodeLengths_length _ 30 15

/-- The dynamic-Huffman code lengths are all ≤ 15 (`computeCodeLengths` caps at
    `maxBits = 15`; the RFC 1951 distance fixup only sets a length to `1`). -/
theorem dynamicCodeLengths_le_15 (litFreqs distFreqs : Array Nat) :
    (∀ x ∈ (dynamicCodeLengths litFreqs distFreqs).1, x ≤ 15) ∧
    (∀ x ∈ (dynamicCodeLengths litFreqs distFreqs).2, x ≤ 15) := by
  refine ⟨Huffman.Spec.computeCodeLengths_bounded _ 286 15 (by omega), ?_⟩
  show ∀ x ∈ (if _ then _ else _), x ≤ 15
  have hbase := Huffman.Spec.computeCodeLengths_bounded
    (freqsToPairs distFreqs) 30 15 (by omega)
  split
  · intro x hx
    rcases List.mem_or_eq_of_mem_set hx with hx1 | hx2
    · exact hbase x hx1
    · omega
  · exact hbase

end Zip.Native.Deflate
