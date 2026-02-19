# Current Plan

<!-- Rewritten at the start of each work session. -->
<!-- If a session ends with unchecked items, the next session continues here. -->

## Status: In progress

## Session type: implementation

## Objective

Prove the remaining `sorry`s in the Huffman specification. Both reduce to
the `nextCodes` recurrence invariant: `nc[b] + count[b] ≤ 2^b`.

## Completed this session

- [x] Fix `count_foldl_mono` build error (simp made no progress after cases)
- [x] Fix `offset_of_lt` build errors (hs₂ needed simp, ih argument ordering)
- [x] `codeFor_injective` structurally complete (modulo `code_value_bound`)
- [x] `canonical_prefix_free` same-length case proved
- [x] Build and test pass, sorry count unchanged at 2

## Remaining: nextCodes recurrence analysis

### Step 1: Simple recursive model

Define `ncRec : Array Nat → Nat → Nat` matching the `nextCodes.go` recurrence
but with simple structural recursion on the bit-length parameter.

### Step 2: Equivalence with nextCodes

Prove `(nextCodes blCount maxBits)[b]! = ncRec blCount b` for `1 ≤ b ≤ maxBits`
by induction on the `go` loop, carrying a loop invariant that tracks which
array entries have been written.

### Step 3: Closed-form / sum characterization

Prove `ncRec blCount b = ∑_{i=0}^{b-1} blCount[i]! * 2^(b-i)` by induction.
Then `ncRec blCount b + blCount[b]! = ∑_{i=0}^{b} blCount[i]! * 2^(b-i)`.

### Step 4: Kraft inequality bound

Show `(∑_{i=0}^{b} blCount[i]! * 2^(b-i)) * 2^(maxBits-b) ≤ 2^maxBits`
by relating the partial sum to the Kraft sum in `ValidLengths`.

### Step 5: Offset bound

Show offset (foldl count over take) < countLengths[len] since sym itself
contributes. This gives `nc[len] + offset < nc[len] + count ≤ 2^len`.

### Step 6: Different-length prefix-free case

Show `ncRec blCount b ≥ (ncRec blCount a + blCount[a]) * 2^(b-a)` for a < b.
This means no code at length a can be a prefix of a code at length b.

## Failed approaches (for future reference)

- `apply ih n (s₂ - 1)` with bullet goals: Lean doesn't assign goals in
  argument order when using `apply`. Use `exact ih ... (by omega) ... _` instead.
- `simp only [hx, ite_false]` after `cases hx : (x == len)` with false branch:
  `cases` already reduces the ite, so simp makes no progress. Just use the
  result directly.
- `simp only [List.length_cons] at hs₁` without also simplifying `hs₂`:
  omega can't relate `(x :: xs).length` to `xs.length` without the simp.
