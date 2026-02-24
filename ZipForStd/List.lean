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

end List
