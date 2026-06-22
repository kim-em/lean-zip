import Zip.Spec.InflateCanonical
import Zip.Native.InflateTreeFree

/-!
# Tree-free canonical decode: correctness

Proves the tree-free canonical decoder (`Zip.Native.InflateTreeFree`) decodes
exactly like the Huffman tree walk, with the tree (`fromLengthsTree lengths`) as a
**proof-only** object — never built at runtime. The chain, bottom-up:

1. `buildFirstIndex` / `buildSymbols` structure invariants (counting sort places
   each symbol at `firstIndex[len] + offset`).
2. arithmetic ↔ `codeFor`: a matched code value `c` of length `len` selects the
   symbol whose canonical codeword is `natToBits c len`.
3. `walkCanonical = (fromLengthsTree lengths).decode` on the fallback bits, hence
   the tree-free decoder equals the canonical `decodeHuffman` spec.

Reuses the `#2679` foundation: `nextCodes` / `countLengths` / `codeFor` /
`allCodes` / `fromLengths_hasLeaf` / `fromLengths_leaf_spec`.
-/

namespace Zip.Native.HuffTree

/-! ## `buildFirstIndex` structure invariant -/

/-- `psumCount count n = ∑_{k=1}^{n} count[k]!` — the cumulative symbol count
    through length `n`, so `firstIndex[len]` is `psumCount count (len-1)`. -/
def psumCount (count : Array Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => psumCount count n + count[n + 1]!

/-- The `buildFirstIndex` loop fills `fi[L] = psumCount count (L-1)` for every
    `1 ≤ L ≤ maxBits`, the offset where length-`L` symbols begin in `symbols`. -/
theorem buildFirstIndex_go_spec (count : Array Nat) (maxBits : Nat) :
    ∀ (n len idx : Nat) (fi : Array Nat), maxBits + 1 - len ≤ n → 1 ≤ len →
      fi.size = maxBits + 2 →
      idx = psumCount count (len - 1) →
      (∀ L, 1 ≤ L → L < len → fi[L]! = psumCount count (L - 1)) →
      ∀ L, 1 ≤ L → L ≤ maxBits →
        (buildFirstIndex.go count maxBits len idx fi)[L]! = psumCount count (L - 1) := by
  intro n
  induction n with
  | zero =>
    intro len idx fi hn hlen1 hsz hidx hfi L hL1 hLmax
    rw [buildFirstIndex.go, if_pos (by omega)]
    exact hfi L hL1 (by omega)
  | succ n ih =>
    intro len idx fi hn hlen1 hsz hidx hfi L hL1 hLmax
    rw [buildFirstIndex.go]
    by_cases hgt : len > maxBits
    · rw [if_pos hgt]; exact hfi L hL1 (by omega)
    · rw [if_neg hgt]
      refine ih (len + 1) (idx + count[len]!) (fi.set! len idx) (by omega) (by omega)
        (by rw [Array.size_set!]; exact hsz) ?_ ?_ L hL1 hLmax
      · -- idx + count[len]! = psumCount count len
        rw [hidx]
        obtain ⟨len', rfl⟩ : ∃ m, len = m + 1 := ⟨len - 1, by omega⟩
        simp only [Nat.add_sub_cancel, psumCount]
      · -- fi.set! len idx preserves the invariant and extends it to len
        intro L' hL'1 hL'lt
        by_cases hL'len : L' = len
        · subst hL'len
          rw [Array.getElem!_set!_self _ _ _ (by rw [hsz]; omega), hidx]
        · rw [Array.getElem!_set!_ne _ _ _ _ (by omega)]
          exact hfi L' hL'1 (by omega)

/-- `buildFirstIndex count maxBits`'s `L`-th entry is the cumulative count of
    symbols of length `< L`. -/
theorem buildFirstIndex_spec (count : Array Nat) (maxBits L : Nat)
    (hL1 : 1 ≤ L) (hLmax : L ≤ maxBits) :
    (buildFirstIndex count maxBits)[L]! = psumCount count (L - 1) :=
  buildFirstIndex_go_spec count maxBits (maxBits + 1) 1 0 (Array.replicate (maxBits + 2) 0)
    (by omega) (by omega) (Array.size_replicate) (by simp [psumCount])
    (fun _ h1 hlt => by omega) L hL1 hLmax

end Zip.Native.HuffTree
