/-!
# List lemmas for the standard library

Generic lemmas about `List.foldl` that are useful beyond the Huffman module.
Candidates for upstreaming to Lean's standard library.
-/

namespace List

/-- A `foldl` that accumulates `init + f x` commutes with the initial value:
    the result is `init` plus the fold starting from `0`. -/
theorem foldl_add_init (f : Nat → Nat) (init : Nat) (ls : List Nat) :
    ls.foldl (fun acc l => acc + f l) init =
      init + ls.foldl (fun acc l => acc + f l) 0 := by
  induction ls generalizing init with
  | nil => simp only [foldl_nil, Nat.add_zero]
  | cons x xs ih => simp only [foldl_cons, Nat.zero_add]; rw [ih, ih (f x)]; omega

/-- A `foldl` that counts elements equal to `b` commutes with the initial value. -/
theorem foldl_count_init (b : Nat) (init : Nat) (ls : List Nat) :
    ls.foldl (fun acc l => if (l == b) = true then acc + 1 else acc) init =
      init + ls.foldl (fun acc l => if (l == b) = true then acc + 1 else acc) 0 := by
  induction ls generalizing init with
  | nil => simp only [beq_iff_eq, foldl_nil, Nat.add_zero]
  | cons x xs ih =>
    simp only [foldl_cons, Nat.zero_add]
    split
    · rw [ih, ih 1]; omega
    · exact ih init

/-! ## getLast -/

/-- `getLast?.getD default` equals `getLast!` for non-empty lists. -/
theorem getLast?_getD_eq_getLast! [Inhabited α] (l : List α) (h : l.length > 0) :
    l.getLast?.getD default = l.getLast! := by
  induction l with
  | nil => simp only [length_nil, gt_iff_lt, Nat.lt_irrefl] at h
  | cons a as ih =>
    cases as with
    | nil => rfl
    | cons b bs => simp [List.getLast?, List.getLast!]

/-! ## foldl-set lemmas -/

/-- `foldl set` preserves list length. -/
theorem foldl_set_length (positions : List Nat) (f : Nat → α) (init : List α) :
    (positions.foldl (fun a pos => a.set pos (f pos)) init).length = init.length := by
  induction positions generalizing init with
  | nil => simp only [foldl_nil]
  | cons p ps ih => simp [ih, List.length_set]

/-- At a position not in the fold list, the value is unchanged from init. -/
theorem foldl_set_getElem_not_mem (positions : List Nat) (f : Nat → α)
    (init : List α) (p : Nat) (hp : p ∉ positions) (hlt : p < init.length) :
    (positions.foldl (fun a pos => a.set pos (f pos)) init)[p]'(by
      rw [foldl_set_length]; exact hlt) = init[p] := by
  induction positions generalizing init with
  | nil => simp only [foldl_nil]
  | cons q qs ih =>
    simp only [List.mem_cons, not_or] at hp
    simp only [List.foldl_cons]
    have hlt' : p < (init.set q (f q)).length := by simp [List.length_set]; exact hlt
    rw [ih (init.set q (f q)) hp.2 hlt']
    exact List.getElem_set_ne (Ne.symm hp.1) _

/-- At a position in the fold list (with nodup), the value is `f p`. -/
theorem foldl_set_getElem_mem (positions : List Nat) (f : Nat → α)
    (init : List α) (p : Nat) (hp : p ∈ positions) (hnodup : positions.Nodup)
    (hlt : p < init.length) (hbounds : ∀ q ∈ positions, q < init.length) :
    (positions.foldl (fun a pos => a.set pos (f pos)) init)[p]'(by
      rw [foldl_set_length]; exact hlt) = f p := by
  induction positions generalizing init with
  | nil => simp only [not_mem_nil] at hp
  | cons q qs ih =>
    simp only [List.mem_cons] at hp
    simp only [List.foldl_cons]
    rw [List.nodup_cons] at hnodup
    have hlt' : p < (init.set q (f q)).length := by simp [List.length_set]; exact hlt
    have hbounds' : ∀ r ∈ qs, r < (init.set q (f q)).length := by
      intro r hr; simp [List.length_set]; exact hbounds r (List.mem_cons_of_mem _ hr)
    cases hp with
    | inl heq =>
      subst heq
      rw [foldl_set_getElem_not_mem qs f _ p hnodup.1 hlt']
      exact List.getElem_set_self _
    | inr hmem =>
      exact ih (init.set q (f q)) hmem hnodup.2 hlt' hbounds'

/-! ## take-set lemma -/

/-- Setting index `idx` and taking `idx + 1` gives the original prefix plus the new value. -/
theorem take_set_succ (l : List α) (idx : Nat) (val : α)
    (hidx : idx < l.length) :
    (l.set idx val).take (idx + 1) = l.take idx ++ [val] := by
  rw [List.take_set, List.take_add_one]
  simp only [List.getElem?_eq_getElem (by omega)]
  rw [List.set_append]
  have h_take_len : (l.take idx).length = idx := List.length_take_of_le (by omega)
  simp only [h_take_len, Nat.lt_irrefl, ↓reduceIte, Nat.sub_self,
             Option.toList, List.set_cons_zero]

/-! ## Prefix comparability -/

/-- Two prefixes of the same list are comparable: one is a prefix of the other. -/
theorem IsPrefix_of_IsPrefix_append {a b : List α} {c : List α}
    (ha : a <+: b ++ c) : a <+: b ∨ b <+: a := by
  induction a generalizing b with
  | nil => left; exact nil_prefix
  | cons x xs ih =>
    cases b with
    | nil => right; exact nil_prefix
    | cons y ys =>
      obtain ⟨t, ht⟩ := ha
      have hxy : x = y := by simp [cons_append] at ht; exact ht.1
      have hrest : xs <+: ys ++ c :=
        ⟨t, by simp [cons_append] at ht; exact ht.2⟩
      cases ih hrest with
      | inl h =>
        left; obtain ⟨t', ht'⟩ := h
        exact ⟨t', by rw [hxy, cons_append, ht']⟩
      | inr h =>
        right; obtain ⟨t', ht'⟩ := h
        exact ⟨t', by rw [← hxy, cons_append, ht']⟩

/-! ## flatMap with uniform-length outputs -/

/-- Dropping `n * k` elements from a flatMap with uniform-length-`k` outputs
    skips exactly `n` segments. -/
theorem flatMap_drop_mul (l : List α) (f : α → List β)
    (k n : Nat) (hk : ∀ a, (f a).length = k) :
    (l.flatMap f).drop (n * k) = (l.drop n).flatMap f := by
  induction n generalizing l with
  | zero => simp only [Nat.zero_mul, drop_zero]
  | succ m ih =>
    cases l with
    | nil => simp only [flatMap_nil, drop_nil]
    | cons a rest =>
      simp only [flatMap_cons, drop_succ_cons]
      have hk_eq : (m + 1) * k = (f a).length + m * k := by
        rw [Nat.succ_mul, hk a, Nat.add_comm]
      rw [hk_eq, ← drop_drop, drop_left]
      exact ih rest

/-- Dropping past a prefix of known length. -/
theorem drop_append_left' {l₁ l₂ : List α} {k : Nat}
    (h : l₁.length = k) (n : Nat) :
    (l₁ ++ l₂).drop (k + n) = l₂.drop n := by
  rw [← drop_drop, drop_left' h]

/-- Dropping `i * k` elements from a flatMap with uniform-length output
    gives the `i`-th element's image followed by the rest. -/
theorem flatMap_uniform_drop {f : α → List β} (hf : ∀ a, (f a).length = k)
    (l : List α) (i : Nat) (hi : i < l.length) :
    (l.flatMap f).drop (i * k) = f l[i] ++ (l.flatMap f).drop ((i + 1) * k) := by
  induction l generalizing i with
  | nil => simp only [length_nil, Nat.not_lt_zero] at hi
  | cons b rest ih =>
    cases i with
    | zero =>
      simp only [flatMap_cons, Nat.zero_mul, drop_zero, getElem_cons_zero,
        Nat.zero_add, Nat.one_mul]
      rw [drop_left' (hf b)]
    | succ j =>
      simp only [flatMap_cons, getElem_cons_succ]
      rw [show (j + 1) * k = k + j * k from by rw [Nat.succ_mul, Nat.add_comm],
          drop_append_left' (hf b),
          show (j + 2) * k = k + (j + 1) * k from by rw [show j + 2 = (j + 1) + 1 from rfl,
            Nat.succ_mul, Nat.add_comm],
          drop_append_left' (hf b)]
      exact ih j (by simpa using hi)

/-- If `l.drop n = a :: rest`, then `rest = l.drop (n + 1)`. -/
theorem drop_cons_tail {l : List α} {a : α} {rest : List α} {n : Nat}
    (h : l.drop n = a :: rest) : rest = l.drop (n + 1) := by
  have : l.drop (n + 1) = (l.drop n).drop 1 := by rw [drop_drop, Nat.add_comm]
  rw [this, h, drop_one, tail_cons]

end List
