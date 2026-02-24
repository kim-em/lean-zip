import Zip.Spec.HuffmanKraft

/-!
# Huffman Code Property Theorems

Property theorems for the canonical Huffman code construction:
prefix-free proofs, injectivity, and decode correctness.

Kraft inequality infrastructure is in `Zip.Spec.HuffmanKraft`.
Definitions and types are in `Zip.Spec.Huffman`.
-/

namespace Huffman.Spec

/-! ## natToBits prefix properties -/

/-- `natToBits val (w₁ + w₂)` splits into the high `w₁` bits
    (of `val / 2^w₂`) followed by the low `w₂` bits. -/
private theorem natToBits_append (val w₁ w₂ : Nat) :
    natToBits val (w₁ + w₂) = natToBits (val / 2 ^ w₂) w₁ ++ natToBits val w₂ := by
  induction w₁ with
  | zero => simp [natToBits]
  | succ n ih =>
    rw [Nat.add_right_comm]
    simp only [natToBits]
    rw [ih, List.cons_append, ← Nat.testBit_div_two_pow]

/-- If `natToBits a n` is a prefix of `natToBits b m` (`n ≤ m`, both values
    in range), then `b < (a + 1) * 2^(m - n)`.  This is the numerical
    consequence of one codeword being a prefix of another. -/
private theorem natToBits_prefix_lt (a b n m : Nat)
    (hnm : n ≤ m) (ha : a < 2 ^ n) (hb : b < 2 ^ m)
    (hpre : (natToBits a n).IsPrefix (natToBits b m)) :
    b < (a + 1) * 2 ^ (m - n) := by
  let d := m - n
  have hd_pos : 0 < 2 ^ d := Nat.two_pow_pos d
  have hm : m = n + d := by omega
  rw [hm, natToBits_append b n d] at hpre
  obtain ⟨t, ht⟩ := hpre
  have ⟨heq, _⟩ := List.append_inj ht (by simp [natToBits_length])
  have hdiv_bound : b / 2 ^ d < 2 ^ n := by
    rw [Nat.div_lt_iff_lt_mul hd_pos, ← Nat.pow_add]; rw [hm] at hb; exact hb
  have ha_eq : a = b / 2 ^ d := natToBits_injective a (b / 2 ^ d) n ha hdiv_bound heq
  have := Nat.lt_mul_div_succ b hd_pos
  rw [ha_eq, Nat.mul_comm]; exact this

/-! ## Prefix comparison lemmas -/

/-- Two prefixes of the same list are comparable: one is a prefix of the other. -/
private theorem IsPrefix_dichotomy {a b c : List Bool}
    (ha : a <+: b ++ c) : a <+: b ∨ b <+: a := by
  induction a generalizing b with
  | nil => left; exact List.nil_prefix
  | cons x xs ih =>
    cases b with
    | nil => right; exact List.nil_prefix
    | cons y ys =>
      obtain ⟨t, ht⟩ := ha
      have hxy : x = y := by simp [List.cons_append] at ht; exact ht.1
      have hrest : xs <+: ys ++ c :=
        ⟨t, by simp [List.cons_append] at ht; exact ht.2⟩
      cases ih hrest with
      | inl h =>
        left; obtain ⟨t', ht'⟩ := h
        exact ⟨t', by rw [hxy, List.cons_append, ht']⟩
      | inr h =>
        right; obtain ⟨t', ht'⟩ := h
        exact ⟨t', by rw [← hxy, List.cons_append, ht']⟩

/-- `isPrefixOf` returns true for a list prepended to any suffix. -/
private theorem isPrefixOf_self_append (cw rest : List Bool) :
    isPrefixOf cw (cw ++ rest) = true := by
  induction cw with
  | nil => simp [isPrefixOf]
  | cons x xs ih => simp [isPrefixOf, ih]

/-! ## Helper lemmas for codeFor proofs -/

/-- The counting foldl is monotone: the result is always ≥ the initial value. -/
protected theorem count_foldl_mono (len : Nat) (l : List Nat) (init : Nat) :
    init ≤ l.foldl (fun acc x => if (x == len) = true then acc + 1 else acc) init := by
  induction l generalizing init with
  | nil => simp
  | cons x xs ih =>
    simp only [List.foldl_cons]
    cases hx : (x == len)
    · exact ih init
    · exact Nat.le_trans (by omega) (ih (init + 1))

/-- If s₁ < s₂ and lengths[s₁] = len, then the offset (count of same-length
    earlier symbols) for s₂ is strictly greater than for s₁, because
    lengths.take s₂ includes symbol s₁ (which has length len). -/
private theorem offset_of_lt (lengths : List Nat) (s₁ s₂ : Nat) (len : Nat)
    (hs₁ : s₁ < lengths.length)
    (hlen₁ : lengths[s₁] = len) (hlt : s₁ < s₂) (hs₂ : s₂ ≤ lengths.length) :
    List.foldl (fun acc l => if (l == len) = true then acc + 1 else acc)
      0 (List.take s₁ lengths) <
    List.foldl (fun acc l => if (l == len) = true then acc + 1 else acc)
      0 (List.take s₂ lengths) := by
  suffices ∀ (init : Nat),
      List.foldl (fun acc l => if (l == len) = true then acc + 1 else acc)
        init (List.take s₁ lengths) <
      List.foldl (fun acc l => if (l == len) = true then acc + 1 else acc)
        init (List.take s₂ lengths) from this 0
  induction lengths generalizing s₁ s₂ with
  | nil => simp at hs₁
  | cons x xs ih =>
    intro init
    cases s₁ with
    | zero =>
      simp only [List.take_zero, List.foldl_nil, List.getElem_cons_zero] at hlen₁ ⊢
      rw [List.take_cons (by omega : 0 < s₂)]
      simp only [List.foldl_cons, show (x == len) = true from beq_iff_eq.mpr hlen₁, ite_true]
      exact Nat.lt_of_lt_of_le (by omega) (Huffman.Spec.count_foldl_mono len _ _)
    | succ n =>
      simp only [List.length_cons] at hs₁ hs₂
      rw [List.take_cons (by omega : 0 < n + 1), List.take_cons (by omega : 0 < s₂)]
      simp only [List.foldl_cons]
      have hlen₁' : xs[n] = len := by
        simp only [List.getElem_cons_succ] at hlen₁; exact hlen₁
      exact ih n (s₂ - 1) (by omega) hlen₁' (by omega) (by omega) _

/-- Extract `len ≠ 0 ∧ len ≤ maxBits` from the codeFor condition. -/
protected theorem codeFor_len_bounds {len maxBits : Nat}
    (h : ¬(len == 0 || decide (len > maxBits)) = true) : len ≠ 0 ∧ len ≤ maxBits := by
  simp only [Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq, not_or] at h; omega

/-- The code value assigned by the canonical construction fits in `len` bits.
    This follows from the Kraft inequality: the nextCodes construction ensures
    nc[len] + count_at_len ≤ 2^len, and offset < count_at_len. -/
protected theorem code_value_bound (lengths : List Nat) (maxBits sym : Nat)
    (hv : ValidLengths lengths maxBits)
    (hs : sym < lengths.length)
    (hlen : ¬(lengths[sym] == 0 || decide (lengths[sym] > maxBits)) = true) :
    (nextCodes (countLengths lengths maxBits) maxBits)[lengths[sym]]! +
      List.foldl (fun acc l => if (l == lengths[sym]) = true then acc + 1 else acc)
        0 (List.take sym lengths) <
    2 ^ lengths[sym] := by
  have ⟨hlen0, hlenM⟩ := Huffman.Spec.codeFor_len_bounds hlen
  have hncBound := Huffman.Spec.nextCodes_plus_count_le lengths maxBits lengths[sym] hv hlen0 hlenM
  have hOffsetLt : List.foldl (fun acc l => if (l == lengths[sym]) = true then acc + 1 else acc)
      0 (List.take sym lengths) <
    lengths.foldl (fun acc l => if (l == lengths[sym]) = true then acc + 1 else acc) 0 := by
    have h := offset_of_lt lengths sym lengths.length lengths[sym] hs rfl hs (by omega)
    rwa [List.take_length] at h
  omega

/-- Extract structural information from `codeFor` returning `some`. -/
protected theorem codeFor_spec {lengths : List Nat} {maxBits sym : Nat} {cw : Codeword}
    (h : codeFor lengths maxBits sym = some cw) :
    ∃ (hs : sym < lengths.length)
      (hlen : ¬(lengths[sym] == 0 || decide (lengths[sym] > maxBits)) = true),
      cw = natToBits
        ((nextCodes (countLengths lengths maxBits) maxBits)[lengths[sym]]! +
          List.foldl (fun acc l => if (l == lengths[sym]) = true then acc + 1 else acc)
            0 (List.take sym lengths))
        lengths[sym] := by
  unfold codeFor at h
  split at h
  · rename_i hs
    simp only [] at h
    split at h
    · simp at h
    · rename_i hlen
      exact ⟨hs, hlen, by simpa using h.symm⟩
  · simp at h

/-! ## Specification theorems -/

/-- `isPrefixOf` agrees with the `List.IsPrefix` proposition. -/
theorem isPrefixOf_iff (pre xs : List Bool) :
    isPrefixOf pre xs = true ↔ pre.IsPrefix xs := by
  induction pre generalizing xs with
  | nil => simp [isPrefixOf, List.IsPrefix]
  | cons a as ih =>
    cases xs with
    | nil => simp [isPrefixOf, List.IsPrefix]
    | cons b bs =>
      simp [isPrefixOf, Bool.and_eq_true, beq_iff_eq, ih]

/-- Decoding with a prefix-free code table is deterministic:
    if `decode` returns a result, it is the unique matching entry. -/
theorem decode_deterministic {α : Type} (table : List (Codeword × α))
    (bits : Codeword) (a b : α) (r₁ r₂ : Codeword) :
    decode table bits = some (a, r₁) →
    decode table bits = some (b, r₂) →
    a = b ∧ r₁ = r₂ := by
  intro h₁ h₂; simp_all

/-- The canonical code assigns distinct codewords to distinct symbols,
    provided the lengths are valid. -/
theorem codeFor_injective (lengths : List Nat) (maxBits : Nat)
    (hv : ValidLengths lengths maxBits)
    (s₁ s₂ : Nat) (cw : Codeword) :
    codeFor lengths maxBits s₁ = some cw →
    codeFor lengths maxBits s₂ = some cw →
    s₁ = s₂ := by
  intro h₁ h₂
  have ⟨hs₁, hlen₁, h₁⟩ := Huffman.Spec.codeFor_spec h₁
  have ⟨hs₂, hlen₂, h₂⟩ := Huffman.Spec.codeFor_spec h₂
  have heq := h₁.symm.trans h₂
  have hlen_eq : lengths[s₁] = lengths[s₂] := by
    have := congrArg List.length heq
    rwa [natToBits_length, natToBits_length] at this
  have hb₁ := Huffman.Spec.code_value_bound lengths maxBits s₁ hv hs₁ hlen₁
  rw [hlen_eq] at heq hb₁
  have hb₂ := Huffman.Spec.code_value_bound lengths maxBits s₂ hv hs₂ hlen₂
  have hcode := natToBits_injective _ _ _ hb₁ hb₂ heq
  by_cases heqs : s₁ = s₂
  · exact heqs
  · exfalso
    have : s₁ < s₂ ∨ s₂ < s₁ := by omega
    cases this with
    | inl hlt =>
      have := offset_of_lt lengths s₁ s₂ lengths[s₂] hs₁ hlen_eq hlt (Nat.le_of_lt hs₂)
      omega
    | inr hgt =>
      have := offset_of_lt lengths s₂ s₁ lengths[s₂] hs₂ rfl hgt (Nat.le_of_lt hs₁)
      omega

/-- The canonical code is prefix-free when lengths are valid. This is
    the key property ensuring unambiguous decoding. -/
theorem canonical_prefix_free (lengths : List Nat) (maxBits : Nat)
    (hv : ValidLengths lengths maxBits)
    (s₁ s₂ : Nat) (cw₁ cw₂ : Codeword) :
    codeFor lengths maxBits s₁ = some cw₁ →
    codeFor lengths maxBits s₂ = some cw₂ →
    s₁ ≠ s₂ →
    ¬cw₁.IsPrefix cw₂ := by
  intro h₁ h₂ hne hpre
  have ⟨hs₁, hlen₁_cond, hcw₁⟩ := Huffman.Spec.codeFor_spec h₁
  have ⟨hs₂, hlen₂_cond, hcw₂⟩ := Huffman.Spec.codeFor_spec h₂
  have ⟨hlen₁_ne, hlen₁_le⟩ := Huffman.Spec.codeFor_len_bounds hlen₁_cond
  have ⟨hlen₂_ne, hlen₂_le⟩ := Huffman.Spec.codeFor_len_bounds hlen₂_cond
  have hlen₁ : cw₁.length = lengths[s₁] := by rw [hcw₁, natToBits_length]
  have hlen₂ : cw₂.length = lengths[s₂] := by rw [hcw₂, natToBits_length]
  obtain ⟨t, ht⟩ := hpre
  have htlen : cw₁.length + t.length = cw₂.length := by
    rw [← ht, List.length_append]
  by_cases heq : lengths[s₁] = lengths[s₂]
  · have : t = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst this; simp at ht; subst ht
    exact hne (codeFor_injective lengths maxBits hv s₁ s₂ cw₁ h₁ h₂)
  · have hlt_len : lengths[s₁] < lengths[s₂] := by omega
    have hb₁ := Huffman.Spec.code_value_bound lengths maxBits s₁ hv hs₁ hlen₁_cond
    have hb₂ := Huffman.Spec.code_value_bound lengths maxBits s₂ hv hs₂ hlen₂_cond
    have hupper := natToBits_prefix_lt _ _ _ _ (by omega) hb₁ hb₂ (hcw₁ ▸ hcw₂ ▸ ⟨t, ht⟩)
    let blCount := countLengths lengths maxBits
    have hnc₁ := Huffman.Spec.nextCodes_eq_ncRec blCount maxBits _ hlen₁_ne hlen₁_le
    have hnc₂ := Huffman.Spec.nextCodes_eq_ncRec blCount maxBits _ hlen₂_ne hlen₂_le
    have hoff_lt : List.foldl (fun acc l => if (l == lengths[s₁]) = true then acc + 1 else acc)
        0 (List.take s₁ lengths) < blCount[lengths[s₁]]! := by
      have h := offset_of_lt lengths s₁ lengths.length lengths[s₁] hs₁ rfl hs₁ (by omega)
      rw [List.take_length] at h
      rw [Huffman.Spec.countLengths_eq lengths maxBits lengths[s₁] hlen₁_ne hlen₁_le]; exact h
    exfalso
    rw [hnc₁, hnc₂] at hupper
    have hmul : (Huffman.Spec.ncRec blCount lengths[s₁] +
        List.foldl (fun acc l => if (l == lengths[s₁]) = true then acc + 1 else acc) 0
          (List.take s₁ lengths) + 1) *
        2 ^ (lengths[s₂] - lengths[s₁]) ≤
        (Huffman.Spec.ncRec blCount lengths[s₁] + blCount[lengths[s₁]]!) *
          2 ^ (lengths[s₂] - lengths[s₁]) :=
      Nat.mul_le_mul_right _ (by omega)
    have hshift := Huffman.Spec.ncRec_shift blCount lengths[s₁] lengths[s₂] hlt_len
    omega

/-! ## Decode correctness -/

/-- `decode` on a prefix-free code table correctly finds the matching entry.
    If `(cw, sym)` is in the table and the codewords are pairwise
    non-prefix, then decoding `cw ++ rest` returns `(sym, rest)`. -/
theorem decode_prefix_free {α : Type} (table : List (Codeword × α))
    (cw : Codeword) (sym : α) (rest : Codeword)
    (hmem : (cw, sym) ∈ table)
    (hpf : ∀ cw₁ s₁ cw₂ s₂, (cw₁, s₁) ∈ table → (cw₂, s₂) ∈ table →
      (cw₁, s₁) ≠ (cw₂, s₂) → ¬cw₁.IsPrefix cw₂) :
    decode table (cw ++ rest) = some (sym, rest) := by
  induction table with
  | nil => simp at hmem
  | cons entry entries ih =>
    obtain ⟨cw', sym'⟩ := entry
    simp only [decode]
    cases hmem with
    | head =>
      simp [isPrefixOf_self_append, List.drop_append_of_le_length (Nat.le_refl _)]
    | tail _ htail =>
      by_cases heq : (cw', sym') = (cw, sym)
      · obtain ⟨rfl, rfl⟩ := Prod.mk.inj heq
        simp [isPrefixOf_self_append, List.drop_append_of_le_length (Nat.le_refl _)]
      · have hno : isPrefixOf cw' (cw ++ rest) = false := by
          cases hp : isPrefixOf cw' (cw ++ rest) with
          | false => rfl
          | true =>
            exfalso; rw [isPrefixOf_iff] at hp
            cases IsPrefix_dichotomy hp with
            | inl h =>
              exact hpf cw' sym' cw sym (List.mem_cons_self ..)
                (List.mem_cons_of_mem _ htail) heq h
            | inr h =>
              exact hpf cw sym cw' sym' (List.mem_cons_of_mem _ htail)
                (List.mem_cons_self ..) (Ne.symm heq) h
        simp only [hno]
        exact ih htail (fun cw₁ s₁ cw₂ s₂ h₁ h₂ hne =>
          hpf cw₁ s₁ cw₂ s₂ (List.mem_cons_of_mem _ h₁)
            (List.mem_cons_of_mem _ h₂) hne)

/-! ## Connecting canonical_prefix_free to allCodes -/

/-- Membership in `allCodes` is characterized by `codeFor`. -/
theorem allCodes_mem_iff (lengths : List Nat) (maxBits : Nat) (s : Nat) (cw : Codeword) :
    (s, cw) ∈ allCodes lengths maxBits ↔
      s < lengths.length ∧ codeFor lengths maxBits s = some cw := by
  simp only [allCodes, List.mem_filterMap, List.mem_range]
  constructor
  · rintro ⟨sym, hsym, h⟩
    cases hcf : codeFor lengths maxBits sym with
    | none => simp [hcf] at h
    | some cw' =>
      simp [hcf] at h
      exact ⟨h.1 ▸ hsym, h.1 ▸ h.2 ▸ hcf⟩
  · rintro ⟨hs, hcode⟩
    exact ⟨s, hs, by simp [hcode]⟩

/-- `allCodes` has no duplicate entries (each symbol appears at most once). -/
theorem allCodes_nodup (lengths : List Nat) (maxBits : Nat) :
    (allCodes lengths maxBits).Nodup := by
  simp only [allCodes, List.Nodup]
  apply List.Pairwise.filterMap (R := (· ≠ ·))
  · intro sym₁ sym₂ hne p₁ hp₁ p₂ hp₂
    cases hc₁ : codeFor lengths maxBits sym₁ with
    | none => simp [hc₁] at hp₁
    | some cw₁ =>
      cases hc₂ : codeFor lengths maxBits sym₂ with
      | none => simp [hc₂] at hp₂
      | some cw₂ =>
        simp [hc₁] at hp₁; simp [hc₂] at hp₂
        subst hp₁; subst hp₂
        exact fun h => hne (Prod.mk.inj h).1
  · exact List.nodup_range

/-- Codewords assigned to distinct symbols are not prefixes of each other.
    This is the membership-based version of `canonical_prefix_free`. -/
theorem allCodes_prefix_free_of_ne (lengths : List Nat) (maxBits : Nat)
    (hv : ValidLengths lengths maxBits)
    (s₁ s₂ : Nat) (cw₁ cw₂ : Codeword)
    (h₁ : (s₁, cw₁) ∈ allCodes lengths maxBits)
    (h₂ : (s₂, cw₂) ∈ allCodes lengths maxBits)
    (hne : s₁ ≠ s₂) :
    ¬cw₁.IsPrefix cw₂ := by
  rw [allCodes_mem_iff] at h₁ h₂
  exact canonical_prefix_free lengths maxBits hv s₁ s₂ cw₁ cw₂ h₁.2 h₂.2 hne

/-- The list of codewords produced by `allCodes` is prefix-free. -/
theorem allCodeWords_prefix_free (lengths : List Nat) (maxBits : Nat)
    (hv : ValidLengths lengths maxBits) :
    IsPrefixFree ((allCodes lengths maxBits).map Prod.snd) := by
  intro i j hi hj hij hpre
  simp only [List.length_map] at hi hj
  rw [List.getElem_map, List.getElem_map] at hpre
  have hmi := (allCodes_mem_iff ..).mp (List.getElem_mem (h := hi))
  have hmj := (allCodes_mem_iff ..).mp (List.getElem_mem (h := hj))
  have hne : (allCodes lengths maxBits)[i].1 ≠ (allCodes lengths maxBits)[j].1 := by
    intro heq
    have hcw_eq := Option.some.inj (hmi.2.symm.trans (heq ▸ hmj.2))
    have hentry_eq : (allCodes lengths maxBits)[i] = (allCodes lengths maxBits)[j] :=
      Prod.ext heq hcw_eq
    have hpw := List.pairwise_iff_getElem.mp (allCodes_nodup lengths maxBits)
    have : ¬(i < j) := fun h => hpw i j hi hj h hentry_eq
    have : ¬(j < i) := fun h => hpw j i hj hi h hentry_eq.symm
    omega
  exact canonical_prefix_free lengths maxBits hv _ _ _ _ hmi.2 hmj.2 hne hpre

end Huffman.Spec
