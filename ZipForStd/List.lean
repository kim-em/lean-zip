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
  | nil => simp
  | cons x xs ih => simp only [foldl_cons, Nat.zero_add]; rw [ih, ih (f x)]; omega

/-- A `foldl` that counts elements equal to `b` commutes with the initial value. -/
theorem foldl_count_init (b : Nat) (init : Nat) (ls : List Nat) :
    ls.foldl (fun acc l => if (l == b) = true then acc + 1 else acc) init =
      init + ls.foldl (fun acc l => if (l == b) = true then acc + 1 else acc) 0 := by
  induction ls generalizing init with
  | nil => simp
  | cons x xs ih =>
    simp only [foldl_cons, Nat.zero_add]
    split
    · rw [ih, ih 1]; omega
    · exact ih init

/-! ## foldl-set lemmas -/

/-- `foldl set` preserves list length. -/
theorem foldl_set_length (positions : List Nat) (f : Nat → α) (init : List α) :
    (positions.foldl (fun a pos => a.set pos (f pos)) init).length = init.length := by
  induction positions generalizing init with
  | nil => simp
  | cons p ps ih => simp [ih, List.length_set]

/-- At a position not in the fold list, the value is unchanged from init. -/
theorem foldl_set_getElem_not_mem (positions : List Nat) (f : Nat → α)
    (init : List α) (p : Nat) (hp : p ∉ positions) (hlt : p < init.length) :
    (positions.foldl (fun a pos => a.set pos (f pos)) init)[p]'(by
      rw [foldl_set_length]; exact hlt) = init[p] := by
  induction positions generalizing init with
  | nil => simp
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
  | nil => simp at hp
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

end List
