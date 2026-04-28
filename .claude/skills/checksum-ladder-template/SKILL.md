---
name: checksum-ladder-template
description: Use when adding a new concrete-shape closed-form rung to a checksum ladder — Adler-32, CRC32, or any future checksum with a Spec/Native split (e.g. XxHash). Covers the three-part Spec identity → Native bridge → public wrapper template, the hypothesis-bearing invariant pattern, `@[simp]` and visibility discipline, and the boundary where the template stops applying (non-Nat algebra).
allowed-tools: Read, Edit, Write, Bash, Grep, Glob
---

# Checksum Ladder Template

A ladder is a family of closed-form theorems for a checksum, each
rung characterizing the checksum on a more interesting byte pattern
(empty → singleton → pair → replicate → combine). Once a ladder
reaches three data points the shape stabilises — this skill records
that shape so new rungs can be landed without re-deriving it.

Seven in-tree examples across two ladders:

| Ladder    | Rungs                                                                        |
|-----------|------------------------------------------------------------------------------|
| Adler-32  | `_empty`, `_singleton`, `_pair`, `_replicate_zero`, `_replicate`, `_combine` |
| CRC32     | `_empty`, `_singleton`, `_pair`                                              |

Trigger this skill when writing any new rung on one of those
ladders, extending to a new checksum, or reviewing a PR that adds
one.

## The Three-Part Shape

Every rung that's landed has the same three parts:

1. **Spec identity** — the closed-form equation, stated and proved
   at the Spec level with no dependency on `Native`. Sits in
   `Zip/Spec/<Checksum>.lean`. Induction, arithmetic, `bv_decide`,
   whatever it takes.
2. **Native bridge** — a thin wrapper in
   `Zip/Native/<Checksum>.lean` that reuses the per-checksum bridge
   lemma to lift the Spec identity to the `ByteArray`-level Native
   API. Typically 5–15 LOC. Pure plumbing.
3. **Public wrapper / API surface** — in some rungs the Native
   bridge *is* the user-facing signature (`_combine`); in others
   it's a mirror of the Spec equation with `ByteArray` arguments.
   Either way, the public signature avoids `let`-destructuring
   (see the let-binding rule below).

### Per-ladder bridge lemma

| Ladder   | Bridge lemma                                                                | Location                                               |
|----------|-----------------------------------------------------------------------------|--------------------------------------------------------|
| Adler-32 | `Native.updateBytes_eq_updateList`                                          | `Zip/Native/Adler32.lean`                           |
| CRC32    | `Native.updateBytes_eq_updateList` + `Spec.crcByteTable_mkTable_eq_crcByte` | `Zip/Native/Crc32.lean` + `Zip/Spec/Crc32.lean` |

The Native bridge proof is almost always

```lean
simp only [<checksumFn>, updateBytes_eq_updateList, <any_init_unpack_rewrite>]
exact Spec.<rung_name> <args>
```

If your new bridge is more than ~15 LOC, something is wrong —
either the Spec identity is still missing a reduction step, or the
bridge is doing work that belongs on the Spec side. Don't paper
over it with bigger `simp only` kits at the Native level.

## Hypothesis-Bearing Variants

Closed forms with a gate (`hn : n < 65521`,
`hA ∧ hB : 1 + n·b < 65521 ∧ n + T(n)·b < 65521`,
`b.toNat < 256`) are proved by:

1. Strengthen the statement to hold over a **free starting state**
   rather than the ladder's canonical `init`.
2. Induct on the pattern's inductive parameter (`List.length`,
   `Nat` count, etc.).
3. Instantiate the strengthened invariant at the starting state the
   rung actually cares about.

Canonical examples:

- **`Spec.checksum_replicate_zero`** (`Zip/Spec/Adler32.lean`)
  uses

  ```lean
  have hstate : ∀ (m k : Nat), k + m < 65521 →
      updateList (1, k) (List.replicate m 0) = (1, k + m) := by
    intro m
    induction m with
    | zero => intros; rfl
    | succ m ih => …
  ```

  Free starting state `k`; induct on `m`; instantiate at `k = 0`.

- **`Spec.checksum_replicate`** (`Zip/Spec/Adler32.lean`) raises
  the bar — the strengthened invariant is

  ```lean
  have hstate : ∀ (m a bsum : Nat),
      a + m * b.toNat < 65521 →
      bsum + m * a + (m * (m + 1) / 2) * b.toNat < 65521 →
      updateList (a, bsum) (List.replicate m b) =
        (a + m * b.toNat, bsum + m * a + (m * (m + 1) / 2) * b.toNat)
  ```

  Both components free; joint hypotheses for the bound preservation;
  instantiated at `(a, bsum) = (1, 0)` for the public statement.

The pattern generalises: if a bound hypothesis appears on the
public statement, expect the Spec-level induction to float it to
the strengthened lemma and carry it through the inductive step.

## `let`-Binding Placement

`let`-bindings belong on the **Spec side**; the public API stays
flat. `Spec.checksum_combine` introduces five Spec-level
`let`-bindings (`a1`, `a2`, `b1`, `b2`, `n`) to keep the equation
readable, while the user-facing `Native.adler32_combine_eq_concat`
(`Zip/Native/Adler32.lean`) is projection-free:

```lean
theorem adler32_combine_eq_concat (xs ys : ByteArray) :
    adler32_combine (adler32 1 xs) (adler32 1 ys) ys.size
      = adler32 1 (xs ++ ys)
```

The Spec side pays the destructuring tax so the Native API doesn't.
Rationale: a flat Native signature is easier to `rw` through in
downstream proofs; `let ⟨a1, a2⟩ := …` on the public surface forces
a dependent-match dance at every call site. (See PR #1700 review
§D for the full argument — that review fixed the shape at this
convention.)

## `@[simp]` Discipline

**Only the `_empty` rung is `@[simp]`.** Every other rung is
untagged, on both Spec and Native sides.

| Rung              | Tag         |
|-------------------|-------------|
| `_empty`          | `@[simp]`   |
| `_singleton`      | (untagged)  |
| `_pair`           | (untagged)  |
| `_replicate_zero` | (untagged)  |
| `_replicate`      | (untagged)  |
| `_combine`        | (untagged)  |
| `_append`         | (untagged)  |

Why: on `_empty`, `LHS = checksum [] = 1` (or `0`) is strictly
simpler than any concrete input. On every other rung, the closed
form's RHS (two table lookups, triangular-number arithmetic, etc.)
is more complex than the plain `checksum xs` LHS. Tagging `@[simp]`
would send `simp` in the wrong direction. See PR #1700 review §E
for the full audit.

## Visibility Ratchet

Keep supporting helpers `private` until a **second cross-file
consumer** materialises. Don't pre-promote.

Existing promotions (triggered by the second consumer, not the
first):

- `Spec.mkTable_size` (`Zip/Spec/Crc32.lean`) — promoted to
  non-private when `Native.crc32_singleton` needed it in addition
  to `Spec.checksum_singleton`.
- `Spec.xor_ff_byte_lt_mkTable_size` (`Zip/Spec/Crc32.lean`) —
  same trigger; promoted on first cross-file use.
- `Spec.crcByteTable_mkTable_eq_crcByte`
  (`Zip/Spec/Crc32.lean`) — promoted in the `_pair` wave when a
  second call site appeared.

Good counter-example: `Spec.pack_toNat_of_bounds`
(`Zip/Spec/Adler32.lean`) — used by every Adler-32 rung proof
but **stays `private`** because all consumers live in the same
file. Visibility is about cross-file need, not call count.

Don't promote in anticipation — a rung that *might* be written next
month is not a consumer. Promote when you land the second consumer
in the same PR.

## When NOT to Apply the Template

The template characterises checksums whose state evolves via
**Nat arithmetic**. It breaks at the boundary where the algebra
becomes multiplicative in a finite field.

- **CRC32 `_replicate_zero` / `_replicate` / `_combine`** need
  GF(2)[x] polynomial multiplication modulo the CRC polynomial.
  The concrete-shape ladder does not extend to those rungs. See
  the `_singleton` review (PR #1697) for the boundary call:

  > A full `checksum_replicate` for CRC32 would require polynomial
  > multiplication modulo `POLY` and is deferred indefinitely.

  That's the stop line. `_empty`, `_singleton`, `_pair` are the
  only concrete-shape CRC32 rungs the template produces.

- Any future checksum whose update function is not a fold over
  byte-wise Nat arithmetic will likely hit the same wall. The
  diagnostic: can you write a closed form for the state after
  `n` copies of a fixed byte using only `Nat.add`, `Nat.mul`,
  `%`, and the triangular-number identity? If yes, the template
  applies; if the closed form forces you into a matrix power or
  a polynomial GCD, it doesn't.

Don't try to force the template onto the wrong side of this line.
The next dedicated meditate scope is the place for a GF(2)[x]
design; do not open that scope mid-ladder.

## Worked Examples

### 1. Adler-32 `_singleton` — simplest concrete rung

| Role          | Symbol                      | File:line                    |
|---------------|-----------------------------|------------------------------|
| Spec identity | `Spec.checksum_singleton`   | `Zip/Spec/Adler32.lean`  |
| Native bridge | `Native.adler32_singleton`  | `Zip/Native/Adler32.lean` |

Spec proof: unfold `checksum` / `updateList` / `updateByte` on a
one-element list, use `pack_toNat_of_bounds` to push the packing
into `Nat`, finish with `omega`. Native proof is three lines —
unfold `adler32`, use the bridge lemma, `exact` the Spec identity.

### 2. Adler-32 `_replicate` — hypothesis-bearing rung

| Role          | Symbol                     | File:line                    |
|---------------|----------------------------|------------------------------|
| Spec identity | `Spec.checksum_replicate`  | `Zip/Spec/Adler32.lean`  |
| Native bridge | `Native.adler32_replicate` | `Zip/Native/Adler32.lean` |

Demonstrates the strengthened-invariant pattern above. Joint
hypotheses `hA, hB` on the public statement; Spec proof lifts to a
free-state invariant `∀ m a bsum, …` with the same two bounds as
induction premises. Native bridge remains ~9 LOC.

### 3. Adler-32 `_combine` — the API-shape rung

| Role           | Symbol                             | File:line                     |
|----------------|------------------------------------|-------------------------------|
| Spec identity  | `Spec.checksum_combine`            | `Zip/Spec/Adler32.lean`   |
| Native def     | `Native.adler32_combine`           | `Zip/Native/Adler32.lean` |
| Native theorem | `Native.adler32_combine_eq_concat` | `Zip/Native/Adler32.lean` |

Illustrates the let-binding placement rule — the Spec theorem uses
five `let`-bindings, the Native API is flat. Note the shape change:
the Native side introduces a new `def` (`adler32_combine`) as the
user-facing combine, and the theorem characterises it by equating
to `adler32 1 (xs ++ ys)`. The Native "bridge" is therefore closer
to 25 LOC than the usual 5–15, because it also has to unpack the
two input checksums back into running states — still pure
plumbing, just more of it.

### 4. CRC32 `_pair` — two table lookups, for contrast

| Role          | Symbol                | File:line                   |
|---------------|-----------------------|-----------------------------|
| Spec identity | `Spec.checksum_pair`  | `Zip/Spec/Crc32.lean`   |
| Native bridge | `Native.crc32_pair`   | `Zip/Native/Crc32.lean` |

Uses both bridge lemmas (`crcByteTable_mkTable_eq_crcByte` +
`updateBytes_eq_updateList`) because CRC32 has a separate
table-equivalence identity the Spec file re-exports. Shows the
template surviving the extra bridge hop without deformation.

## Review Checklist

When reviewing a new rung or writing one yourself, confirm:

- [ ] Spec identity proved without importing `Native`.
- [ ] Native bridge is 5–15 LOC (or 20–25 LOC for `_combine`-shape
      rungs that build a new `def`); if larger, suspect the Spec
      side is incomplete.
- [ ] Hypothesis-bearing rung uses the strengthened-invariant
      pattern; bound hypotheses are induction premises, not
      `by omega` post-hoc.
- [ ] `@[simp]` tagged **only** if the rung is `_empty`.
- [ ] Supporting helpers are `private` unless a second cross-file
      consumer lands in the same PR.
- [ ] Public API signature is projection-free / destructuring-free;
      `let`-bindings live on the Spec side only.
- [ ] If attempting a rung beyond the template's boundary (CRC32
      `_replicate*` / `_combine`), stop — that's a separate
      GF(2)[x] design scope.

## Non-goals

This skill does **not** cover:

- CRC32 GF(2)[x] polynomial-ring design — separate meditate scope.
- Native implementation choices (SIMD, table size, unrolling) —
  concerns of the runtime optimiser, not the characterising theorem.
- Checksum conformance tests (`ZipTest/NativeChecksum.lean`) — the
  rung-landing PR owns those, but the template is about the proofs.
