---
name: lean-dependent-types
description: Use when Lean 4 gives "motive is not type correct", max recursion on List.ofFn, rewriting fails due to dependent types, or cross-file visibility issues with private/protected.
allowed-tools: Read, Bash, Grep
---

# Lean 4 Dependent Type and Visibility Patterns

## `congr` Max Recursion on Nested `Prod` in `Option`

`congr 1; congr 1` on `some (a, b, c) = some (x, y, z)` hits max recursion depth.
Use `congrArg some (Prod.ext ?_ (Prod.ext ?_ rfl))` instead — gives clean sub-goals
without recursion issues. Note: `congrArg` not `congr_arg`.

## `rw`/`▸` Max Recursion on `List.ofFn`

Rewriting a term containing `List.ofFn (fun (i : Fin n) => complex_expr)` can hit
max recursion depth because the motive involves dependent types.
Fix: use `set_option maxRecDepth 2048 in` before the `have`/tactic that performs
the rewrite. `▸` is even worse than `rw` here since it triggers full `whnf`.

## Namespace Scoping for New Definitions

`def Foo.Bar.baz` inside `namespace Quux` creates `Quux.Foo.Bar.baz`, NOT `Foo.Bar.baz`.
To define in a different namespace, either close the current namespace first, or use
a local name (e.g. `def decodeBits` instead of `def Zip.Native.HuffTree.decodeBits`).

## `protected` Not `private` for Cross-File Access

When a definition or lemma in one file is needed by another, use `protected` visibility.
`private` makes it inaccessible from other files. This applies to both:
- Lemmas (e.g. `byteToBits_length` used in BitstreamCorrect and InflateCorrect)
- Definitions referenced in proof hypotheses (e.g. native table constants like
  `lengthBase`, `distExtra` in Inflate.lean that appear in `decodeHuffman.go` —
  if they're `private`, proofs in InflateCorrect.lean can't name them in `cases`
  or `simp` arguments)

**Caveat**: `protected` requires fully-qualified names even within the same namespace
(`Inflate.lengthBase` instead of `lengthBase`). For definitions used unqualified within
their own namespace AND needed cross-file, use public (no modifier) instead.

## `▸` Rewrites in the Wrong Direction for Transitive Equality

When proving `br'.data = br.data` by chaining `br'.data = br₁.data` and
`br₁.data = br.data`, do NOT use `hd' ▸ hd₁ ▸ rfl` — `▸` rewrites in the wrong
direction, changing dependent types in the goal (e.g. `br'.data.size` becomes
`br.data.size` when you need the reverse).

Use `exact hd'.trans hd₁` or `exact ⟨hd'.trans hd₁, ...⟩` instead.

This applies generally: `▸` is designed for rewriting the goal by substituting
the LHS of an equation with the RHS. For transitive equality chains, `.trans` is
always cleaner and avoids dependent-type issues.

## `exact` vs `have :=` for Wildcard Resolution

`exact f _ _ _` does goal-directed elaboration — wildcards are resolved from the
expected goal type.

`have := f _ _ _` elaborates independently and fails when wildcards can't be inferred
from the function signature alone (e.g., complex expressions like hash table states
from `updateHashes`).

When applying a recursive lemma whose arguments include complex intermediate state,
prefer `exact` (possibly via a helper lemma) over `have :=`. For arithmetic wrappers
around recursive calls, extract a helper like `length_cons_le_of_advance` and use:
```lean
exact helper (recursive_lemma _ _ _ _ _) (by omega) hle
```
