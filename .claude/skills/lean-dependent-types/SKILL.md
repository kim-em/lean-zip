---
name: lean-dependent-types
description: Use when Lean 4 gives "motive is not type correct", max recursion on List.ofFn, rewriting fails due to dependent types, or cross-file visibility issues with private/protected.
allowed-tools: Read, Bash, Grep
---

# Lean 4 Dependent Type and Visibility Patterns

## `congr` max recursion on nested `Prod` in `Option`

`congr 1; congr 1` on `some (a, b, c) = some (x, y, z)` hits max recursion depth.
Use instead:

```lean
congrArg some (Prod.ext ?_ (Prod.ext ?_ rfl))
```

Gives clean sub-goals without recursion. Note: `congrArg`, not `congr_arg`.

## `rw`/`▸` max recursion on `List.ofFn` and large constant tables

Rewriting a term containing `List.ofFn (fun (i : Fin n) => ...)` or large constant
lists (e.g. 288-element `fixedLitLengths`) can hit `maxRecDepth` because the motive
traverses the whole structure. `▸` is worse than `rw` here (it triggers full `whnf`).

Fixes:
- `set_option maxRecDepth 2048 in` before the `have`/tactic doing the rewrite.
- Lift the equality through the outer function instead of rewriting inside the term:
  ```lean
  have := congrArg (Huffman.Spec.codeFor · 15 s) fixedLitLengths_eq
  ```
- For theorems over large tables (288 literals, 32 distances) you may also need
  `maxRecDepth 4096` and `maxHeartbeats 4000000`.

## `subst` before `cases` to avoid alpha-equivalence mismatch

When composing two-block theorems, a step theorem produces output with `if let`
expressions containing proof variables whose names differ from the theorem
statement's elaboration. The match motives differ in alpha-equivalence even though
both types **print identically**.

**Symptom**: `exact`, `by exact`, and direct application of a single-block theorem
all fail after applying a step theorem, despite the goal appearing to match.

**Fix**: `subst` the intermediate position variable *before* `cases` on the `if let`
discriminant, so the variable is eliminated before Lean elaborates the match:

```lean
theorem f_two_block ... := by
  rw [step_theorem ...]
  -- Goal now has: if let some ht := huffTree1 then some ht else prevHuff
  subst hpos_eq1              -- eliminate afterHdr1 early, avoids hlit1' creation
  cases huffTree1             -- reduces if let to concrete none/some values
  · exact single_block_none_theorem ...
  · exact single_block_some_theorem ...
```

Without `subst`, the `if let` captures earlier proof parameters (e.g. `hlit1`) as
match scrutinees, creating a motive that differs from the single-block theorem's
context. See `decompressBlocksWF_succeeds_compressed_zero_seq_then_compressed_zero_seq`
in `Zip/Spec/Zstd.lean`.

A related variant: if `subst` is not available, inline the two-step proof rather
than calling the composition theorem, bridging with `(by cases huffTree1 <;> exact hlit2)`.
See `decompressFrame_compressed_seq_then_compressed_lit_content` in `Zip/Spec/Zstd.lean`.

## `protected` not `private` for cross-file access

When a definition or lemma in one file is needed by another, use `protected`.
`private` makes it inaccessible from other files. Applies to:
- Lemmas (e.g. `byteToBits_length` used across BitstreamCorrect and InflateCorrect).
- Definitions named in proof hypotheses (e.g. native table constants `lengthBase`,
  `distExtra` in Inflate.lean appearing in `decodeHuffman.go` — if `private`, proofs
  in InflateCorrect.lean can't name them in `cases` or `simp` arguments).

**Caveat**: `protected` requires fully-qualified names even within the same namespace
(`Inflate.lengthBase`, not `lengthBase`). For a definition used unqualified within its
own namespace AND needed cross-file, use public (no modifier).

## Namespace scoping for new definitions

`def Foo.Bar.baz` inside `namespace Quux` creates `Quux.Foo.Bar.baz`, not `Foo.Bar.baz`.
Close the current namespace first, or use a local name.

## `.trans` not `▸` for transitive equality chains

`▸` rewrites the goal LHS→RHS and flips dependent types the wrong way (e.g.
`br'.data.size` becomes `br.data.size` when you need the reverse). For a chain
`br'.data = br₁.data`, `br₁.data = br.data`, use `exact hd'.trans hd₁`, not
`hd' ▸ hd₁ ▸ rfl`.

## `letFun` for `have` bindings in unfolded definitions

When `unfold f at h` leaves `have x := e; body` bindings, they appear as `letFun`.
Reduce with `simp only [letFun] at h`. The `unusedHavesSuffice` linter may flag
`letFun` as unused here — false positive; it is needed.

## `exact` vs `have :=` for wildcard resolution

`exact f _ _ _` does goal-directed elaboration — wildcards resolve from the expected
goal type. `have := f _ _ _` elaborates independently and fails when wildcards can't
be inferred from the signature alone (e.g. hash-table states from `updateHashes`).
For recursive lemmas with complex intermediate state, prefer `exact` (via a helper
if needed):

```lean
exact helper (recursive_lemma _ _ _ _ _) (by omega) hle
```
