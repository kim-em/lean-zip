---
name: lean-array-list
description: Use when Lean 4 proofs involve ByteArray, Array, List indexing, getElem, length lemmas, take/drop, or roundtrip proofs over byte collections.
allowed-tools: Read, Bash, Grep
---

# Lean 4 ByteArray/Array/List Proof Patterns

## ByteArray/Array/List Indexing

- `data.data[pos] = data[pos]` (where `data : ByteArray`) is `rfl`
- For `data.data.toList[pos] = data[pos]`: `simp only [Array.getElem_toList]` suffices
  (as of v4.29.0-rc2; on rc1 a trailing `; rfl` was also needed)
- When `List.getElem_map` is involved (e.g. `(arr.toList.map f)[i] = f arr[i]`):
  `simp only [List.getElem_map, Array.getElem_toList]` closes the goal

## Length Conversions

- `Array.length_toList`: `arr.toList.length = arr.size`
- `List.size_toArray`: `(l.toArray).size = l.length` — bridges Array.size to List.length
  for array literals (`#[a, b, c]` elaborates as `List.toArray [a, b, c]`)
- `ByteArray.size_data`: `ba.data.size = ba.size`
- Chain them for `ba.data.toList.length`

**Concrete array size in `simp only`**: To reduce `#[a, b, ...].size` to a number,
use `List.size_toArray` + `List.length_cons` + `List.length_nil`:
```lean
simp only [myArray, List.size_toArray, List.length_cons, List.length_nil]
-- Reduces #[a, b, c].size to 3
```
Note: `Array.size_toArray` does NOT exist — use `List.size_toArray`.

## `getElem?_pos`/`getElem!_pos` for Array Lookups

To prove `arr[i]? = some arr[i]!`, use the two-step pattern:
```lean
rw [getElem!_pos arr i h]  -- rewrites arr[i]! to arr[i] (bounds-checked)
exact getElem?_pos arr i h  -- proves arr[i]? = some arr[i]
```
`getElem?_pos` needs the explicit container argument (not `_`) to avoid
`GetElem?` type class synthesis failures.

## `getElem!_def` + `getElem?_eq_some_iff` for Panic-Indexed Array Proofs

When proving properties about `arr[idx]!` (panic-indexed access), unfold
with `getElem!_def` and case-split on whether the index is in bounds:

```lean
simp only [getElem!_def]
split
· -- some case: arr[idx]? = some e
  rename_i e he
  obtain ⟨hi, heq⟩ := Array.getElem?_eq_some_iff.mp he
  -- hi : idx < arr.size, heq : arr[idx] = e
  rw [← heq]
  exact some_property ⟨idx, hi⟩
· -- none case: idx ≥ arr.size, result is `default`
  have : (default : MyType).field = 0 := by decide
  omega
```

**Key lemma**: `Array.getElem?_eq_some_iff : xs[i]? = some b ↔ ∃ h, xs[i] = b`

**Common mistake**: Trying `Array.getElem?_eq_some` (doesn't exist),
`Array.get!_pos`/`Array.get!_neg` (don't exist), or
`Array.getElem?_pos` (different type — proves `arr[i]? = some arr[i]`,
not the reverse direction needed here).

## Fin Coercion Mismatch in omega

When a lemma over `Fin n` is applied as `lemma ⟨k, hk⟩`, omega treats
`arr[(⟨k, hk⟩ : Fin n).val]!` and `arr[k]!` as different variables.

Fix by annotating the result type:
```lean
have : arr[k]! ≥ 1 := lemma ⟨k, hk⟩
```
**Critical**: `have := lemma ⟨k, hk⟩` (without type annotation) does NOT work —
the anonymous hypothesis retains the Fin.val form and omega still sees two distinct
variables. Always use the annotated form.

**Deeper mismatch — `GetElem` vs `getInternal`**: After `unfold f at h`, the goal
may use `Array.getInternal` (the raw internal accessor) while a helper lemma uses
`arr[i]'hi` (the `GetElem` typeclass). Even with type annotation, `omega` treats
these as distinct expressions. The fix is `exact` with `Nat.le_trans` (or similar)
instead of `omega`, since `exact` does full definitional unification:

```lean
-- BAD: omega can't unify GetElem-based and getInternal-based array access
have := helper_lemma code hlt  -- uses arr[code]'hlt via GetElem
omega  -- fails: sees arr[code].fst and (arr.getInternal code hlt).fst as distinct

-- GOOD: exact does definitional unification
exact Nat.le_trans (helper_lemma code hlt) (Nat.le_add_right _ _)
```

## `decide_cbv` on Fin-Bounded Array Properties

To verify a property holds for all entries of a concrete array, use `decide_cbv`
on a `Fin`-bounded universal:

```lean
private theorem all_baselines_ge_three :
    ∀ i : Fin myTable.size, (myTable[i.val]'i.isLt).1 ≥ 3 := by
  decide_cbv
```

Then wrap in a Nat-indexed helper to avoid Fin coercion issues in callers:

```lean
private theorem baseline_ge_three (i : Nat) (hi : i < myTable.size) :
    (myTable[i]'hi).1 ≥ 3 :=
  all_baselines_ge_three ⟨i, hi⟩
```

**Key constraints**:
- The `∀ i : Fin n, P i` form is needed for `decide_cbv` — it must be a closed
  proposition (no free Nat variables)
- `decide` (without `_cbv`) has the same constraint but may be slower
- The Nat wrapper eliminates the Fin coercion so callers can use `exact` or
  `Nat.le_trans` without the GetElem/getInternal mismatch

## `List.getElem_of_eq` for Extracting from List Equality

When `hih : l1 = l2` and you need `l1[i] = l2[i]`, use
`List.getElem_of_eq hih hbound` where `hbound : i < l1.length`.
This avoids dependent-type rewriting issues with direct `rw [hih]` on getElem.

## `n + 0` Normalization Breaks `rw` Patterns

As of v4.29.0-rc2, Lean normalizes `n + 0` to `n` earlier. If a lemma's conclusion
contains `arr[pfx.size + k]` and you instantiate `k = 0`, the rewrite target
`arr[pfx.size + 0]` won't match the goal's `arr[pfx.size]`. Fix: add a specialized
`_zero` variant of the lemma that states the result with `arr[pfx.size]` directly.

## `take`/`drop` ↔ `Array.extract`

To bridge `List.take`/`List.drop` (from spec) with `Array.extract` (from native):
```lean
simp only [Array.toList_extract, List.extract, Nat.sub_zero, List.drop_zero]
```
Then `← List.map_drop` + `List.drop_take` for drop-inside-map-take.

## `Array.toArray_toList`

`a.toList.toArray = a` for any Array. Use `Array.toArray_toList`.
NOT `Array.toList_toArray` or `List.toArray_toList` — those don't exist.

## `readBitsLSB_bound` for omega

`readBitsLSB n bits = some (val, rest)` implies `val < 2^n`. Essential for bounding
UInt values (e.g., `hlit_v.toNat < 32`) before omega can prove `≤ UInt16.size`.

## List Nat ↔ Array UInt8 Roundtrip

To prove `l = (l.toArray.map Nat.toUInt8).toList.map UInt8.toNat` when all elements
are ≤ 15 (from `ValidLengths`):
```lean
simp only [Array.toList_map, List.map_map]; symm
rw [List.map_congr_left (fun n hn => by
  show UInt8.toNat (Nat.toUInt8 n) = n
  simp only [Nat.toUInt8, UInt8.toNat, UInt8.ofNat, BitVec.toNat_ofNat]
  exact Nat.mod_eq_of_lt (by have := hv.1 n hn; omega))]
simp  -- closes `List.map (fun n => n) l = l` (not `List.map id l`)
```
Note: `List.map_congr_left` produces `fun n => n` not `id`, so `List.map_id`
won't match — use `simp` instead.

## UInt8→Nat→UInt8 Roundtrip

To prove `Nat.toUInt8 (UInt8.toNat u) = u`:
```lean
unfold Nat.toUInt8 UInt8.ofNat UInt8.toNat
rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]
```
Do NOT use `simp [Nat.toUInt8, UInt8.toNat, ...]` — it loops via
`UInt8.toNat.eq_1` / `UInt8.toNat_toBitVec`. Do NOT try `congr 1` (max recursion)
or `UInt8.ext` / `UInt8.eq_of_toNat_eq` (don't exist).

For lists: `l.map (Nat.toUInt8 ∘ UInt8.toNat) = l` via `List.map_congr_left` with
the above per-element proof, then `simp`.

## ByteArray Concatenation Indexing

When proving properties about concatenated ByteArrays (e.g. `header ++ payload ++ trailer`),
use the `getElem!_append_left`/`getElem!_append_right` chain. Key lemmas (in
`Zip/Spec/BinaryCorrect.lean`):

**Two-part concatenation:**
```lean
getElem!_append_left  (a b : ByteArray) (i : Nat) (h : i < a.size) :
    (a ++ b)[i]! = a[i]!
getElem!_append_right (a b : ByteArray) (i : Nat) (h : i < b.size) :
    (a ++ b)[a.size + i]! = b[i]!
```

**Three-part concatenation** (`a ++ b ++ c`):
```lean
getElem!_append3_left  (a b c) (i) (h : i < a.size) :
    (a ++ b ++ c)[i]! = a[i]!
getElem!_append3_mid   (a b c) (i) (h : i < b.size) :
    (a ++ b ++ c)[a.size + i]! = b[i]!
getElem!_append3_right (a b c) (i) (h : i < c.size) :
    (a ++ b ++ c)[(a ++ b).size + i]! = c[i]!
```

**Reading integers from concatenated arrays:**
```lean
readUInt32LE_append_left   (a b) (offset) (h : offset + 4 ≤ a.size) :
    readUInt32LE (a ++ b) offset = readUInt32LE a offset
readUInt32LE_append_right  (a b) (offset) (h : offset + 4 ≤ b.size) :
    readUInt32LE (a ++ b) (a.size + offset) = readUInt32LE b offset
readUInt32LE_append3_mid   (a b c) (offset) (h : offset + 4 ≤ b.size) :
    readUInt32LE (a ++ b ++ c) (a.size + offset) = readUInt32LE b offset
```

**Pattern for three-part concat proofs** (common in gzip/zlib framing):
1. Unfold the function to expose individual `getElem!` or `readUInt32LE` calls
2. Apply `getElem!_append3_*` or `readUInt32LE_append3_*` lemma for each byte/field
3. Resolve arithmetic offsets with `show a.size + offset + k = a.size + (offset + k) from by omega`
4. Close size bounds with `by simp [ByteArray.size_append]; omega`

**Size of concatenation:**
`ByteArray.size_append : (a ++ b).size = a.size + b.size`

## `get!` ↔ `getD` Bridge (`Array.getElem!_eq_getD`)

`a[i]!` (for types with `Inhabited`) is definitionally `a.getD i default`.
For `Nat`, `default = 0`, so `a[i]! = a.getD i 0` by `rfl`. The library
provides `Array.getElem!_eq_getD : xs[i]! = xs.getD i default`.

**When predicates use `getD` but goals have `get!`** (common when loop
invariants are stated with `getD` but do-notation desugaring produces `get!`):

```lean
-- Direct: get! and getD are definitionally equal for Nat
have hcount : v3[sym]! ≤ bound := h3_counts sym
-- h3_counts : ∀ sym, v3.getD sym 0 ≤ bound
-- Works because v3[sym]! = v3.getD sym 0 definitionally
```

**When you need explicit conversion**: `simp only [Array.getElem!_eq_getD]`
rewrites `a[i]!` to `a.getD i default` in the goal.

## `getD` After `set!` (`Array.getElem?_setIfInBounds`)

`simp only [Array.getElem_setIfInBounds]` often **fails** after
`unfold Array.getD; simp only [Array.size_setIfInBounds]` because the
bound proof gets transported and the simp lemma can't match. This is
because `Array.getElem_setIfInBounds` is `@[grind =]`, not `@[simp]`.

**Workaround**: Prove a `getD`-level helper using `Array.getD_eq_getD_getElem?`
and `Array.getElem?_setIfInBounds` (which IS `@[simp]`-compatible):

```lean
private theorem getD_set! (a : Array Nat) (i v s : Nat) :
    (a.set! i v).getD s 0 = if i = s ∧ i < a.size then v else a.getD s 0 := by
  simp only [Array.set!_eq_setIfInBounds, Array.getD_eq_getD_getElem?,
    Array.getElem?_setIfInBounds]
  split <;> split <;> simp_all <;> intro <;> omega
```

Then use `rw [getD_set!]; split` instead of manual unfolding.

## Singleton Array Fin Elimination

When proving properties about `arr[i]` where `arr` has exactly 1 element and
`i : Fin arr.size`, direct `rw`/`simp` on the index fails due to dependent types
(the bound proof depends on `i`). The solution:

```lean
-- arr has size 1 (by rfl or existing theorem)
have hsz : arr.size = 1 := rfl
-- Construct a Fin with a compatible proof term, prove equality via Fin.ext
have : i = ⟨0, hsz ▸ Nat.zero_lt_one⟩ := Fin.ext (by omega)
-- subst eliminates i entirely, enabling definitional reduction
subst this
-- Now arr[⟨0, _⟩] reduces and `show`/`change` can match the concrete value
show someConcreteValue
```

**Why other approaches fail:**
- `rw [show i.val = 0 from ...]` on `arr[i]` hits dependent type errors
- `simp only [Array.getElem_singleton]` needs Nat indexing, not Fin
- `Fin.getElem_fin` doesn't exist in this toolchain
- `change`/`show` before subst can't reduce `arr[i]` with abstract `i`

**The pattern**: `Fin.ext (by omega)` + `subst` is the reliable way to
eliminate a Fin index in a singleton array. The `hsz ▸ Nat.zero_lt_one`
constructs a proof term that `subst` can handle.

## Build Missing API, Don't Work Around It

If a proof is blocked by missing lemmas for standard types (ByteArray, Array, List,
UInt32, etc.), add the missing lemma to `ZipForStd/` in the appropriate namespace.
For example, if `ByteArray.foldl_toList` is missing, add it in
`ZipForStd/ByteArray.lean` in the `ByteArray` namespace. These lemmas are candidates
for upstreaming to Lean's standard library — write them as if they belonged there.
Don't use workarounds like going through `.data.data.foldl` when the right fix is a
proper API lemma.
