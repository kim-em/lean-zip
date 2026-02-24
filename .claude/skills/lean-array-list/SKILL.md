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
- `ByteArray.size_data`: `ba.data.size = ba.size`
- Chain them for `ba.data.toList.length`

## `getElem?_pos`/`getElem!_pos` for Array Lookups

To prove `arr[i]? = some arr[i]!`, use the two-step pattern:
```lean
rw [getElem!_pos arr i h]  -- rewrites arr[i]! to arr[i] (bounds-checked)
exact getElem?_pos arr i h  -- proves arr[i]? = some arr[i]
```
`getElem?_pos` needs the explicit container argument (not `_`) to avoid
`GetElem?` type class synthesis failures.

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

## Build Missing API, Don't Work Around It

If a proof is blocked by missing lemmas for standard types (ByteArray, Array, List,
UInt32, etc.), add the missing lemma to `ZipForStd/` in the appropriate namespace.
For example, if `ByteArray.foldl_toList` is missing, add it in
`ZipForStd/ByteArray.lean` in the `ByteArray` namespace. These lemmas are candidates
for upstreaming to Lean's standard library — write them as if they belonged there.
Don't use workarounds like going through `.data.data.foldl` when the right fix is a
proper API lemma.
