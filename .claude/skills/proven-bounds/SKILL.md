---
name: proven-bounds
description: Use when converting `]!` runtime bounds checks to proven-bounds `]` access in Lean 4. Covers guard capture, omega proofs, caller propagation, loop bound capture, and common pitfalls.
allowed-tools: Bash, Read, Glob, Grep, Edit, Write
---

# Proven-Bounds Data Access in Lean 4

Converting `xs[i]!` (runtime bounds check, panics on out-of-bounds) to
`xs[i]` (statically proven bounds) by ensuring `i < xs.size` is in scope.

## Core Pattern: Guard Capture with `if h :`

The fundamental technique: use `if h : condition then` to bind a proof.

```lean
-- BEFORE (runtime check)
let val := data[pos]!

-- AFTER (proven bounds)
if h : pos < data.size then
  let val := data[pos]  -- h : pos < data.size is in scope
else
  throw "out of bounds"
```

The colon in `if h :` is critical — plain `if h` captures a `Bool`, not
a `Prop` proof. Only `if h :` (decidable proposition) gives a usable
hypothesis.

## Pattern: Nested Guards in Except Monads

Chain multiple bounds checks, each capturing its own hypothesis:

```lean
if h1 : code < table1.size then
  let v1 := table1[code]
  if h2 : idx < table2.size then
    let v2 := table2[idx]
    -- both h1 and h2 in scope
  else throw "table2 out of range"
else throw "table1 out of range"
```

## Pattern: Loop Bound Capture with `for h : i in`

Use `h :` in `for` loops to capture the loop index bound:

```lean
for h : i in [:data.size] do
  let byte := data[i]  -- h : i < data.size in scope
```

Without `h :`, the loop variable has no proof attached.

## Pattern: Well-Founded Recursion Replacement

`while` and `for` loops generate opaque `loop✝` functions that cannot be
unfolded in proofs. Replace with explicit recursion:

```lean
-- BEFORE (opaque loop)
for i in [:n] do
  result := result.push data[pos + i]!

-- AFTER (proof-friendly recursion)
def copyLoop (data : ByteArray) (pos count : Nat) (dst : ByteArray)
    (i : Nat) : ByteArray :=
  if hi : i < count then
    if hpos : pos + i < data.size then
      copyLoop data pos count (dst.push data[pos + i]) (i + 1)
    else dst
  else dst
termination_by count - i
```

The guard `hi : i < count` provides both the bounds proof and the
termination measure (`count - i` decreases).

## Pattern: Caller Propagation of Size Invariants

When a function receives data whose size is constrained by the caller,
thread the proof through:

```lean
-- Function signature includes size constraint
def processBlock (data : ByteArray) (pos : Nat) (hpos : pos + 3 ≤ data.size) : ... :=
  let byte0 := data[pos]      -- by omega (from hpos)
  let byte1 := data[pos + 1]  -- by omega (from hpos)
  let byte2 := data[pos + 2]  -- by omega (from hpos)
```

When the caller has already verified `pos + 3 ≤ data.size`, passing it
as a hypothesis avoids re-checking at every access site.

## Tactics for Bounds Proofs

- **`omega`**: The primary workhorse. Solves linear arithmetic over `Nat`
  including `i < xs.size` goals when `h : i < xs.size` or similar is in
  scope. Also handles `pos + k < data.size` from `hpos : pos + n ≤ data.size`
  when `k < n`.
- **`Nat.lt_of_lt_of_le`**: When you have `h1 : i < n` and `h2 : n ≤ m`,
  conclude `i < m`. Usually `omega` handles this automatically.
- **`Array.size_set`**: After `arr.set i v`, the size is unchanged:
  `(arr.set i v).size = arr.size`. Useful when proving bounds through
  array mutations.

## Common Pitfalls

### 1. `]!` on derived indices

```lean
if h : i < lengths.size then
  let len := lengths[i]         -- proven bounds (good)
  let code := nextCode[len]!    -- still needs ! (len is a value, not bounded by h)
```

The guard `h : i < lengths.size` only proves bounds for `lengths`, not
for `nextCode`. To prove `nextCode[len]`, you need a separate
`len < nextCode.size` proof.

### 2. `.set!` vs `[]` asymmetry

`Array.set!` and `ByteArray.set!` silently no-op on out-of-bounds.
They never need bounds proofs. Only read access (`[]`) requires proofs.

### 3. UInt conversion opacity

`data[pos.toNat]` where `pos : UInt32` — the `.toNat` conversion makes
the index opaque to `omega`. You may need:
```lean
have : pos.toNat < data.size := by omega  -- if pos < data.size.toUInt32 is known
```

### 4. Termination and bounds are intertwined

The same guard often serves double duty:
```lean
if h : pos < data.size then
  -- h proves data[pos] is valid
  -- h also proves data.size - (pos + 1) < data.size - pos (for termination)
  recurse (pos + 1)
termination_by data.size - pos
decreasing_by omega  -- uses h
```

### 5. Don't convert speculatively

Only convert `]!` to `]` when:
- The function is on the proof path (needs verification)
- The bounds proof is straightforward (guard already exists or `omega` suffices)
- The change doesn't require restructuring the entire function

Mechanical conversion of every `]!` is not always worth the complexity.

### 6. Spec proof repair after conversion

Converting `]!` to `]` changes the term structure, breaking existing proofs:

- **`ite` → `dite`**: `if h : cond` desugars to `dite`, not `ite`. Replace
  `if_pos`/`if_neg` with `dif_pos`/`dif_neg`, and `↓reduceIte` with
  `dite_false`/`dite_true` in simp calls.
- **`getElem!_pos` bridge**: Spec proofs that reference `data[pos]!` can be
  updated using `rw [getElem!_pos data pos (by omega)]` to rewrite
  hypotheses to match the new `data[pos]'(proof)` term.
- **`dite` closure bloat**: `dite` generates larger closure terms than `ite`,
  which can cause `simp only` to exceed step limits. If this happens,
  try `unfold` + `split` instead of `simp only [functionName, ...]`.
- **`forIn` loop body term matching**: Spec proofs using
  `forIn_range_always_ok'` require exact syntactic matching of the loop
  body closure. Changing `data[i]!` to `data[i]'(proof)` inside a loop
  creates a different closure that won't match. You may need to update
  the `suffices` block or refactor to well-founded recursion.

### 7. Internal-guard let-bindings + `split` hostility

The "internal-guard" pattern
`let v := if h : i < xs.size then xs[i]'h else default` is defeq to
`xs[i]!` for `UInt8` (since `default = 0`) and seems like a clean
local conversion. But if any spec proof uses `dsimp only [funcName, ...]`
followed by `split`, the conversion breaks:

1. `dsimp only` performs let-zeta, hoisting the new dite to the top of
   the term tree.
2. `split` greedily consumes the FIRST decidable expression top-down —
   which is now the new internal-guard dite, NOT the intended outer
   guard the proof was written against.
3. Cascading "Application type mismatch" / "simp made no progress"
   errors follow.

This is especially painful when a function has a sibling iterator
implementation (e.g. `funcIter` ≡ `func`) — converting `func` alone
desyncs dite-shapes from `funcIter`, breaking the equivalence proof.
Either change BOTH sides in lockstep, refactor the spec to not rely on
top-level `split`, or skip the conversion. Don't try to land asymmetric
dite-shapes through `dsimp + split` proofs.

### 8. Do-notation guard caveat

In do-notation, `if h : cond then throw "err"` does NOT make `¬cond`
available in the continuation after the `if`. You must use an explicit
`else` branch:
```lean
-- WRONG: ¬cond NOT available after this
if h : cond then throw "err"
let x := ...  -- h is not in scope here

-- RIGHT: ¬cond available in else branch
if h : cond then
  throw "err"
else
  let x := ...  -- h : ¬cond is in scope
```

## Checklist for Conversion

1. Identify all `]!` sites in the target function
2. For each site, determine where the index bound comes from:
   - Direct guard (`if h : i < xs.size`)
   - Caller invariant (function parameter)
   - Arithmetic from other bounds (`omega`)
3. Add `if h :` guards or propagate caller hypotheses as needed
4. Replace `]!` with `]` — Lean will check the proof is in scope
5. If the function uses `for`/`while`, consider refactoring to
   well-founded recursion (see Pattern above)
6. Check for existing spec proofs and plan repair (see pitfall 6)
7. Build and verify: `lake build <module>`
