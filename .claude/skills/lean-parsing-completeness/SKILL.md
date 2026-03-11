---
name: lean-parsing-completeness
description: Use when proving parsing completeness theorems — that a parsing function returns .ok when given well-formed input, or that spec-level success implies native success. Also use when proving position bounds, eliminator lemmas, or chaining monadic parsing steps in Except/Option.
allowed-tools: Read, Edit, Write, Bash, Glob, Grep
---

# Parsing Completeness Proof Patterns

Patterns distilled from 8+ parsing completeness theorems across DEFLATE and
Zstd decoders. These proofs show that when a specification says input is
valid, the native parser succeeds.

## Two Flavours of Completeness

### 1. Spec success implies native success

The spec function returns `some (result, rest)`, prove the native function
returns `.ok (result', state')` with correspondence between result/result'
and rest/state'.

```lean
theorem readBits_complete (br : BitReader) (n val : Nat) (rest : List Bool)
    (hwf : br.bitOff < 8) (hn : n ≤ 32)
    (hspec : Spec.readBitsLSB n br.toBits = some (val, rest)) :
    ∃ br', br.readBits n = .ok (val.toUInt32, br') ∧ br'.toBits = rest := by
```

### 2. Native success implies properties (eliminator lemmas)

The native function returns `.ok`, prove bounds/invariants about the result.

```lean
theorem parseHeader_ok_elim (data : ByteArray) (pos : Nat) (result pos' : ...)
    (h : parseHeader data pos = .ok (result, pos')) :
    pos' ≥ pos + 2 ∧ pos' ≤ data.size := by
```

Both follow the same core proof technique.

## Core Proof Technique

### Step 1: Unfold the parsing function

```lean
simp only [parseFunction, bind, Except.bind] at h
```

Use `simp only` with bind/Except.bind to expose the monadic chain. For
do-notation, this reveals the sequence of operations as nested `match`es.

### Step 2: Eliminate error branches with guard discharge

For each `if guard then ... else throw`:

```lean
by_cases h1 : guard_condition
· rw [if_pos h1] at h; ...   -- success branch
· rw [if_neg h1] at h; exact nomatch h  -- error branch is impossible
```

The hypothesis `h : ... = .ok _` contradicts `throw` via `nomatch`.

### Step 3: Case-split on intermediate results

For each `match intermediateCall with | .ok v => ... | .error e => ...`:

```lean
cases hstep : intermediateCall with
| error e => simp only [hstep] at h; exact nomatch h
| ok v =>
  rw [hstep] at h; dsimp only [Bind.bind, Except.bind] at h
  -- continue with v available
```

### Step 4: Extract equalities from the final pure

At the end of the chain, `h` has the form `pure (result, pos) = .ok (r, p)`.
Extract with:

```lean
simp only [pure, Pure.pure, Except.pure] at h
obtain ⟨rfl, rfl⟩ := h
```

Or for single values: `obtain rfl := h`.

### Step 5: Close with rfl or chain bounds

The goal is now in terms of the extracted values. Close with `rfl`,
`exact ⟨rfl, rfl⟩`, or combine bound lemmas with `omega`.

## Complete Example

```lean
theorem parseLiteralsSection_treeless_complete
    (data : ByteArray) (pos : Nat) (prevHuff : Option ZstdHuffmanTable)
    (section : ZstdLiteralsSection) (pos' : Nat)
    (h : parseLiteralsSection data pos prevHuff = .ok (section, pos')) :
    pos' ≥ pos ∧ pos' ≤ data.size := by
  simp only [parseLiteralsSection, bind, Except.bind] at h
  -- Guard: bounds check
  by_cases h1 : data.size < pos + 1
  · rw [if_pos h1] at h; exact nomatch h
  · rw [if_neg h1] at h
    simp only [pure, Pure.pure, Except.pure] at h
    -- Case split on block type
    by_cases h2 : blockType == 0
    · rw [if_pos h2] at h
      cases hraw : parseRawLiterals data pos with
      | error e => simp only [hraw] at h; exact nomatch h
      | ok v =>
        rw [hraw] at h
        dsimp only [Bind.bind, Except.bind] at h
        obtain ⟨rfl, rfl⟩ := h
        exact ⟨by omega, parseRawLiterals_le_size hraw⟩
    · rw [if_neg h2] at h; ...
```

## Common Sub-Patterns

### PUnit.unit artifacts

Do-notation for side-effect-free binds produces `PUnit.unit`. Clean with:

```lean
simp only [pure, Pure.pure, Except.pure] at h
```

### `getElem!` with bounds

When the function uses `data[pos]!` (panic-indexed), use:

```lean
simp only [getElem!_def] at h
split at h
· -- bounds hold: have the actual element
· -- bounds fail: contradiction with guard
```

### Chaining position bounds

When composing two parsing steps, each with its own `_le_size` lemma:

```lean
have h1_le := step1_le_size hstep1   -- pos₁ ≤ data.size
have h2_le := step2_le_size hstep2   -- pos₂ ≤ data.size
have h1_ge := step1_pos_ge hstep1    -- pos₁ ≥ pos + k₁
have h2_ge := step2_pos_ge hstep2    -- pos₂ ≥ pos₁ + k₂
omega
```

### WF-recursive parsers

For parsers using well-founded recursion (e.g., Huffman tree building),
use `f.induct` for structural induction:

```lean
theorem parseLoop_complete : ... := by
  induction fuel using parseLoop.induct generalizing acc
  · -- base case
  · -- recursive case: unfold one step, apply IH
```

### `BEq` to `Prop` bridging

Guards often use `==` (BEq) but proofs need `=` (Prop). Bridge with:

```lean
simp only [beq_iff_eq] at h2  -- converts (x == y) = true to x = y
```

Or for the negative:

```lean
simp only [bne_iff_ne] at h2
```

### Multiple format cases (sizeFormat pattern)

When a parser dispatches on a format discriminant (e.g., 2-bit sizeFormat):

```lean
by_cases h2 : sizeFormat == 0
· rw [if_pos h2] at h; ...
· rw [if_neg h2] at h
  by_cases h3 : sizeFormat == 1
  · rw [if_pos h3] at h; ...
  · rw [if_neg h3] at h
    by_cases h4 : sizeFormat == 2
    · rw [if_pos h4] at h; ...
    · rw [if_neg h4] at h
      -- last case: sizeFormat == 3 (use omega to establish)
```

## Visibility Requirements

Parsing completeness proofs live in `Zip/Spec/` but reference functions
in `Zip/Native/`. The native parsing functions must NOT be `private`:

- Use **no modifier** (public) for functions referenced in completeness proofs
- If a function was `private`, change it to `protected` or public before
  starting the proof — don't discover this mid-proof

Check visibility early: `grep -n 'private def targetFunction'`.

## Eliminator Lemma Pattern

Factor shared case analysis into a reusable eliminator:

```lean
-- Eliminator: extracts all useful facts from parse success
theorem parseX_ok_elim (h : parseX data pos = .ok (result, pos')) :
    pos' ≥ pos + minSize ∧ pos' ≤ data.size ∧ result.field ∈ validRange := by
  ...

-- Downstream theorems use the eliminator instead of re-analyzing
theorem parseY_complete (h : parseY data pos = .ok ...) : ... := by
  have ⟨hge, hle, hvalid⟩ := parseX_ok_elim hX
  ...
```

This avoids duplicating the same `by_cases`/`cases`/`nomatch` chain in
every theorem that depends on `parseX` succeeding.

### Field characterization from parse success

When proving that a parsed struct's fields equal specific expressions over
the input bytes, after `unfold_except` and `split at h` on the match:

- Success branches give `h : {field1 := ..., field2 := ...} = result ∧ pos+k = afterPos`
- Use `obtain ⟨rfl, rfl⟩ := h` to substitute `result` and `afterPos`
- **Simple field projection** (e.g., `hdr.blockSize = raw >>> 3`): close with `rfl`
- **Conjunction over match branches** (e.g., `(typeVal=0 → .raw) ∧ (typeVal=1 → .rle)`):
  use `simp_all` because you need the `heq✝ : matchDiscrim = N` hypothesis to rule out
  impossible implications

**Always use explicit case split** (not `<;>`) because different branches may need
different closers (`rfl` vs `simp_all` vs `exact nomatch h`).

```lean
-- Example: field characterization for parseBlockHeader
theorem parseBlockHeader_blockType_eq ... := by
  unfold Zip.Native.parseBlockHeader at h
  unfold_except
  split at h
  · exact nomatch h          -- guard failure
  · split at h
    · obtain ⟨rfl, rfl⟩ := h; simp_all  -- typeVal = 0
    · obtain ⟨rfl, rfl⟩ := h; simp_all  -- typeVal = 1
    · obtain ⟨rfl, rfl⟩ := h; simp_all  -- typeVal = 2
    · exact nomatch h                     -- reserved type
```

### Existential goals: use `match hresult` not `simp only`

When the goal has existentials (`∃ x y z, f = .ok (x, y, z)`), do NOT
unfold the function in the goal — `simp only [f, bind, ...]` explodes
because it must distribute under `∃`. Instead, match on the result:

```lean
match hresult : parseFunction data pos with
| .ok (a, b, c) => exact ⟨a, b, c, rfl⟩
| .error _ =>
  exfalso
  simp only [parseFunction, bind, Except.bind, ...] at hresult
  -- Now hresult is a hypothesis, no existentials to blow up
```

### Helper definitions: avoid `let` bindings

Helper definitions used in `hsize` hypotheses (e.g., `rawLiteralsSectionSize`)
must NOT use `let` bindings. After `unfold`/`delta`, `let` bindings become
opaque `have` terms that block `split` from finding `if` expressions.

**Bad** (blocks `split at hsize` after unfolding):
```lean
def rawSize (data : ByteArray) (pos : Nat) : Nat :=
  let sizeFormat := ((data[pos]! >>> 2) &&& 3).toNat
  if sizeFormat == 0 then 1 + ... else ...
```

**Good** (inlines everything so `split` sees the `if` directly):
```lean
def rawSize (data : ByteArray) (pos : Nat) : Nat :=
  if ((data[pos]! >>> 2 &&& 3).toNat == 0) then 1 + ... else ...
```

After `unfold rawSize at hsize; split at hsize`, each branch gets the
concrete value. Use `contradiction` to eliminate branches that conflict
with the outer `split at hresult` context.

### `split at h` auto-resolves with context hypotheses

When `split at h` encounters `if cond then A else B` and the context
already contains `h✝ : cond = true` (or `¬cond = true`), the `if` is
automatically resolved — no second `split` is needed. This happens when
the conditions in a helper definition match conditions from an outer
`split at hresult`.

## Anti-Patterns

### Don't use `simp` to close error branches

`simp` may succeed but is fragile. Prefer `exact nomatch h` — it's
faster, more robust, and communicates intent clearly.

### Don't unfold too deeply

Unfold ONE function at a time. If `parseA` calls `parseB` calls `parseC`,
unfold only `parseA`, then case-split on the `parseB` call. Don't
`simp only [parseA, parseB, parseC]` — the term explodes.

### Don't forget `dsimp only` after `rw`

After `rw [hstep] at h` where `hstep : f = .ok v`, the bind/match may
not reduce automatically. Follow with:

```lean
dsimp only [Bind.bind, Except.bind] at h
```

to collapse `match (.ok v) with | .ok x => ... | .error e => ...`.

## Cross-References

- **lean-monad-proofs**: General `Except`/`Option` bind unfolding
- **lean-zstd-patterns**: Zstd-specific parsing implementation details
- **lean-zstd-spec-pattern**: Spec file structure and naming conventions
- **lean-wf-recursion**: WF function unfolding for recursive parsers
- **lean-fuel-induction**: Fuel-based parser proofs (older pattern)
