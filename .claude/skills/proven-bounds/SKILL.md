---
name: proven-bounds
description: Use when converting `]!` runtime bounds checks to proven-bounds `]` access in Lean 4. Covers guard capture, omega proofs, caller propagation, loop bound capture, and common pitfalls.
allowed-tools: Bash, Read, Glob, Grep, Edit, Write
---

# Proven-Bounds Data Access in Lean 4

Convert `xs[i]!` (runtime check, panics out-of-bounds) to `xs[i]`
(statically proven) by getting `i < xs.size` into scope.

Conversion in brief:
- Find each `]!` site; trace where its index bound comes from (a guard, a
  caller hypothesis, or arithmetic via `omega`).
- Add `if h :` guards / propagate caller hypotheses, then swap `]!` → `]`.
- Refactor `for`/`while` to well-founded recursion if you need the bound in a
  proof (opaque `loop✝` can't be unfolded).
- Repair affected spec proofs (see pitfall: spec repair).
- Don't convert speculatively: only when the function is on the proof path and
  the bound is straightforward. Mechanical conversion of every `]!` is not
  always worth the complexity.

## Core Pattern: Guard Capture with `if h :`

Use `if h : condition then` to bind a proof of the condition.

```lean
-- BEFORE: let val := data[pos]!
if h : pos < data.size then
  let val := data[pos]        -- h : pos < data.size in scope
else
  throw "out of bounds"
```

The colon is critical: plain `if h` captures a `Bool`, not a `Prop` proof.
Only `if h :` (decidable proposition) gives a usable hypothesis.

Nest guards in `Except` monads, each capturing its own hypothesis:

```lean
if h1 : code < table1.size then
  let v1 := table1[code]
  if h2 : idx < table2.size then
    let v2 := table2[idx]     -- both h1 and h2 in scope
  else throw "table2 out of range"
else throw "table1 out of range"
```

## Loop Bound Capture: `for h : i in`

```lean
for h : i in [:data.size] do
  let byte := data[i]         -- h : i < data.size in scope
```

Without `h :`, the loop variable has no proof attached.

## Well-Founded Recursion Replacement

`while`/`for` generate opaque `loop✝` functions that cannot be unfolded in
proofs. Replace with explicit recursion; the guard does double duty as bounds
proof and termination measure:

```lean
def copyLoop (data : ByteArray) (pos count : Nat) (dst : ByteArray)
    (i : Nat) : ByteArray :=
  if hi : i < count then
    if hpos : pos + i < data.size then
      copyLoop data pos count (dst.push data[pos + i]) (i + 1)
    else dst
  else dst
termination_by count - i
```

## Caller Propagation of Size Invariants

When the caller has already verified the size, thread the proof in as a
parameter rather than re-checking at every access:

```lean
def processBlock (data : ByteArray) (pos : Nat) (hpos : pos + 3 ≤ data.size) :=
  let byte0 := data[pos]      -- by omega (from hpos)
  let byte1 := data[pos + 1]  -- by omega
  let byte2 := data[pos + 2]  -- by omega
```

## Generational Guarded Wrapper (when threading would cascade)

Caller propagation only works if you can add the hypothesis to the callers
too. When the function is a **shared helper whose correctness proofs are
stated for an *arbitrary* array** (no size hypothesis — common for heuristic
state like a hash table / `prev` chain / DP cost arrays that "never enter the
proof"), adding a hypothesis in-place cascades it into every such proof
(`mainLoop_valid`, `_encodable`, …) and breaks them.

Instead do generational refinement with a guarded wrapper, three pieces:

```lean
-- 1. Proven-bounds copy: identical body, []! → [], takes the size hypothesis.
def fooFast (...) (hps : pos ≤ prev.size) (...) := ... prev[cand]'(by omega) ...

-- 2. Wrapper with the ORIGINAL signature: one runtime check per OUTER
--    iteration establishes the invariant; fall back to the panic-checked
--    reference when it can't be shown (fallback is unreachable at runtime).
@[inline] def fooGuarded (...) (... no hps ...) :=
  if hps : pos ≤ prev.size then fooFast ... hps ... else foo ...   -- `foo` = reference

-- 3. Equivalence (in the Spec file): wrapper = reference, by `split`.
theorem fooFast_eq    ... : fooFast ... = foo ... := by induction ...
theorem fooGuarded_eq ... : fooGuarded ... = foo ... := by
  unfold fooGuarded; split; · exact fooFast_eq ..; · rfl
```

Runtime (iterative) functions call `fooGuarded`; the reference functions and
**all** their proofs stay untouched. Each iter-vs-reference equivalence proof
gains one line near the top — `simp only [fooGuarded_eq, ...]` rewrites the
wrappers back to the reference, then proceeds verbatim. The single outer-loop
check is amortised over the whole inner loop, so inner accesses are statically
unchecked.

In `fooFast_eq` (a fuel/measure induction) the only per-step difference is
`prev[cand]'h` vs `prev[cand]!`; bridge with `getElem!_pos` (see pitfall
below), then `simp only [Nat.add_sub_cancel, ih]` closes the recursion. If
`fooFast` carries a size hypothesis whose type mentions an array you induct on,
include it in `generalizing` (e.g. `generalizing j hashTable prev hht`).

## Bounds Tactics

`omega` is the workhorse: it solves `i < xs.size` from a matching guard, and
`pos + k < data.size` from `hpos : pos + n ≤ data.size` when `k < n`. After
`arr.set i v`, `Array.size_set` gives `(arr.set i v).size = arr.size` for
reasoning through mutations.

## Pitfalls

### `]!` on derived indices
A guard `h : i < lengths.size` proves bounds only for `lengths`. A read
`nextCode[len]` (where `len := lengths[i]`) needs a separate
`len < nextCode.size` proof.

### `.set!` vs `[]` asymmetry
`Array.set!` / `ByteArray.set!` silently no-op out-of-bounds and never need
proofs. Only read access (`[]`) requires them.

### UInt conversion opacity
`data[pos.toNat]` where `pos : UInt32` — the `.toNat` is opaque to `omega`.
You may need `have : pos.toNat < data.size := by omega` (given a known
`pos < data.size.toUInt32`).

### Do-notation guard: no `¬cond` after a bare `if h : ... then throw`
```lean
-- WRONG: h is NOT in scope below
if h : cond then throw "err"
let x := ...
-- RIGHT: ¬cond available in else
if h : cond then throw "err"
else let x := ...
```

### `unless` rebinds `mut` variables, dropping bounds
Even when its body doesn't touch a `mut` variable, the elaborator threads the
`mut`-state through `unless` and emits a fresh binding in the continuation.
Any bound captured earlier is no longer attached to the `pos` you see after.

```lean
-- WRONG: after the first `unless`, `pos` is a fresh Nat — hHdr no longer helps
if hHdr : pos + 10 ≤ data.size then
  let id1 := data[pos]
  unless id1 == 0x1f do return result
  let id2 := data[pos + 1]   -- bound unprovable: `pos` was rebound
```

Remedy: read every byte you need **before** any control-flow branch that may
rebind the `mut`, then branch on the captured values:

```lean
if hHdr : pos + 10 ≤ data.size then
  let id1 := data[pos]
  let id2 := data[pos + 1]
  let cm  := data[pos + 2]
  unless id1 == 0x1f && id2 == 0x8b do return result
  unless cm == 8 do throw "unsupported"
  pos := pos + 10
```

Symptom: a `data[pos + k]` failing a bounds goal `omega` can't close, despite
an earlier `if h : pos + N ≤ data.size`. Scan upward for the first `unless` (or
`if ... then throw` without `else`) and hoist the reads above it.

### Termination and bounds intertwine
One guard often serves both:
```lean
if h : pos < data.size then recurse (pos + 1)
termination_by data.size - pos
decreasing_by omega   -- uses h
```

### Spec proof repair after conversion
Converting `]!` → `]` changes term structure and breaks existing proofs:
- **`ite` → `dite`**: `if h : cond` desugars to `dite`. Replace
  `if_pos`/`if_neg` with `dif_pos`/`dif_neg`, and `↓reduceIte` with
  `dite_false`/`dite_true`.
- **`getElem!_pos` bridge**: rewrite `data[pos]!` references with
  `rw [getElem!_pos data pos (by omega)]` to match the new `data[pos]'(proof)`.
- **`dite` closure bloat**: `dite` makes larger closures than `ite`, which can
  push `simp only` past step limits. Try `unfold` + `split` instead of
  `simp only [functionName, ...]`.
- **`forIn` loop body matching**: `forIn_range_always_ok'` needs exact
  syntactic match of the body closure. Changing `data[i]!` to `data[i]'(proof)`
  inside a loop yields a different closure that won't match — update the
  `suffices` block or refactor to well-founded recursion.

### `@[expose]` combinators (e.g. `List.pmap`) break `rfl` specs
Inlining an `@[expose]` combinator like `List.pmap` inside a def whose spec
ends in `rfl` can trigger `maximum recursion depth has been reached` during
elaboration: `@[expose]` eagerly unfolds on both sides of the equality and the
kernel recurses through the `pmap` skeleton on each side simultaneously.

```lean
def deflateDynamic ... :=
  let litFreqPairs :=
    (List.range litFreqs.size).pmap
      (fun i (h : i < litFreqs.size) => (i, litFreqs[i]'h)) ...
example : deflateDynamic data = ... := by unfold deflateDynamic; rfl  -- BOOM
```

Remedy: hide the `pmap` behind a named helper so the unfolder doesn't recurse
into its body on both sides:

```lean
def freqsToPairs (freqs : Array Nat) : List (Nat × Nat) :=
  (List.range freqs.size).pmap
    (fun i (h : i < freqs.size) => (i, freqs[i]'h))
    (fun _ hi => List.mem_range.mp hi)

def deflateDynamic ... := let litFreqPairs := freqsToPairs litFreqs; ...
```

Expect this when a spec that was `rfl` before conversion now reports `maximum
recursion depth`.

### `let`-bound index blocks `rw [getElem!_pos]`
When bridging `a[i]'h` ↔ `a[i]!` in a `*Fast_eq` proof, the index is usually a
`let`/`have`-bound local from the unfolded body (`let hsh := hash3 …; a[hsh]!`).
`rw [getElem!_pos a hsh h]` **fails to fire** — it wants the unfolded
expression (`hash3 …`), which doesn't match the bound `hsh`. Fold it into a
`simp only`, whose default `zeta` inlines the `let` first:

```lean
-- rw [getElem!_pos hashTable hsh hb]            -- ✗ `hsh` is let-bound, no match
simp only [getElem!_pos hashTable (hash3 data (pos+j) hashSize hd) hb]  -- ✓
```

The bound `hb : index < a.size` is typically `hash3 … < hashSize ≤ a.size`,
i.e. `Nat.mod_lt _ hpos` (hash3's body is `_ % hashSize`) chained by `omega`
with the `hashSize ≤ a.size` invariant.
