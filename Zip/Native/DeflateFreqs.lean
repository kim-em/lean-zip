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

end Zip.Native.Deflate
