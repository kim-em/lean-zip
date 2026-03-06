---
name: lean-wf-recursion
description: Use when Lean 4 proofs involve well-founded recursion, termination_by, f.induct functional induction, WF function unfolding, or converting fuel-based functions to WF recursion.
allowed-tools: Read, Bash, Grep
---

# Lean 4 Well-Founded Recursion Proof Patterns

## Unfolding WF Functions

WF recursive functions have special unfolding behavior. The wrong
tactic will loop or produce unusable goals.

### The Three Strategies

| Tactic | Behavior | When to Use |
|--------|----------|-------------|
| `unfold f` | Single-level unfold of `f` | Default choice for WF functions |
| `rw [f.eq_1]` | Rewrites one application via equation lemma | When `unfold` is too aggressive or inside `conv` |
| `simp only [f]` | **FORBIDDEN** — loops on WF functions | Never for WF functions |

**Why `simp only [f]` loops:** simp repeatedly rewrites `f` in its own
body. For WF functions, the body always contains recursive calls to `f`,
so simp never reaches a fixpoint.

### `unfold` — The Default

```lean
-- Exposes guard conditions for split/cases
unfold tokenFreqs.go
split
· -- guard satisfied: i < tokens.size
  ...
· -- guard failed: ¬(i < tokens.size)
  exact ⟨hlit, hdist⟩
```

After `unfold`, use `split` to case-analyze the exposed `if`/`match`.
See `Zip/Spec/DeflateDynamicFreqs.lean:29`.

### `rw [f.eq_1]` — Precise Rewriting

When `unfold` unfolds ALL occurrences (including recursive calls you
want to keep opaque), use the auto-generated equation lemma instead:

```lean
-- Rewrites exactly one occurrence of kraftSumFrom
rw [kraftSumFrom.eq_1]
exact if_neg (by omega)
```

See `Zip/Spec/HuffmanKraft.lean:74`.

**Multiple equation lemmas:** When `f` pattern-matches on constructors,
Lean generates `f.eq_1`, `f.eq_2`, etc. — one per match arm. Choose the
equation matching your case.

### Standalone Case Lemmas

When `rw [f.eq_1]` produces a goal too large to work with (many
`if`/`match` branches), prove a specialized lemma:

```lean
private theorem f_case2 (xs : List α) (h : ¬(xs.length ≤ N)) :
    f xs = ... body for this case ... := by
  rw [f.eq_1]
  simp only [h, ↓reduceIte, ...]
```

Then `rw [f_case2 _ h]` in the main proof. Used for `encodeStored_non_final`
in `Zip/Spec/Deflate.lean`.

## Functional Induction with `f.induct`

For every WF-recursive function `f`, Lean auto-generates an induction
principle `f.induct` whose cases match the recursion structure.

```lean
theorem encodeStored_go (data : List UInt8) (acc : List UInt8) :
    decode.go (encodeStored data) acc = some (acc ++ data) := by
  induction data using encodeStored.induct generalizing acc with
  | case1 data hle =>
    -- Base case: data.length ≤ 65535
    unfold encodeStored
    simp only [hle, ↓reduceIte]
    ...
  | case2 data hgt rest ih =>
    -- Recursive case: data.length > 65535
    ...
```

See `Zip/Spec/Deflate.lean:585`.

**Key points:**
- `generalizing acc` when the function has accumulator-style parameters
- Each case name matches the recursive structure
- `ih` is the induction hypothesis for recursive calls
- `f.induct` fails to generate if `f`'s termination proof uses `sorry`

### `f.induct` vs Matching `termination_by`

Two ways to do induction matching a WF function:

| Approach | Pros | Cons |
|----------|------|------|
| `induction ... using f.induct` | Cases match `f` exactly; no duplication | Need to learn case names |
| Theorem with same `termination_by` | Familiar; direct recursive calls | Duplicates termination proof |

Both work. Use `f.induct` when the function has complex branching;
use matching `termination_by` for simpler functions where duplicating
the measure is trivial. See `lean-fuel-induction` skill for the
`termination_by` approach.

## Termination Measures

Common measures in this codebase:

| Measure | Example | Used For |
|---------|---------|----------|
| `array.size - i` | `termination_by tokens.size - i` | Array traversal loops |
| `list.length` | `termination_by xs => xs.length` | List consumption |
| `dataSize * 8 - br.bitPos` | Bit stream decoding | Functions that consume bits |
| `totalCodes - acc.length` | `termination_by totalCodes - acc.length` | Bounded accumulator growth |

### The `dataSize` Parameter Pattern

For functions that consume a bit stream, pass `br.data.size` as an
explicit `dataSize` parameter rather than using `br.data.size` directly:

```lean
def decodeHuffman (br : BitReader) ... :=
  go br.data.size br output    -- capture data.size once
where
  go (dataSize : Nat) (br : BitReader) ... :=
    ...
    go dataSize br₁ ...        -- pass through unchanged
  termination_by dataSize * 8 - br.bitPos
```

**Why:** `omega` cannot derive `br'.data.size = br.data.size` without
invariant lemmas. Making `dataSize` a fixed parameter avoids this
dependency entirely. See `Zip/Native/Inflate.lean:261`.

## Dependent `if` Guards and `dif_pos`/`dif_neg`

WF functions often use dependent `if` to bind proof witnesses:

```lean
if _h : bits'.length < bits.length then
  decodeSymbols ... bits' ...   -- _h proves termination
else
  none
```

### Resolving Guards in Proofs

Use `dif_pos`/`dif_neg` to select branches of dependent `if`:

```lean
-- In hypothesis: prove guard is true, then simplify
by_cases hlt : bits'.length < bits.length
· simp only [dif_pos hlt] at h
  ...
· simp only [dif_neg hlt] at h
  ...
```

Or when you can prove the guard directly:

```lean
have hlen : (restBits ++ rest).length < (symBits ++ restBits ++ rest).length := by
  have hpos := encodeLitLen_nonempty ...
  simp [List.length_append]; omega
rw [dif_pos hlen]
```

See `Zip/Spec/DeflateEncode.lean:543` and `Zip/Spec/DeflateSuffix.lean:142`.

### `split at h` for `if` in Hypotheses

When a hypothesis contains an `if` from a WF function, `split at h`
case-analyzes it directly:

```lean
split at ht
· -- guard satisfied branch
  simp at ht; ...
· -- guard failed branch
  simp at ht; ...
```

This replaces the old `guard` + `by_cases` pattern from fuel-based code.
See `Zip/Spec/LZ77NativeCorrect.lean:335`.

## `↓reduceIte` Limitation with Bool-to-Prop

`↓reduceIte` reduces `if True/False then ...` but NOT `if (false = true) then ...`.

The `false = true` form arises when a Bool equality becomes a Prop via
coercion. Fix with explicit `if_neg`:

```lean
-- BAD: ↓reduceIte cannot reduce this
simp only [↓reduceIte]  -- no progress on `if (false = true) then ...`

-- GOOD: resolve the Prop explicitly
simp only [if_neg (show ¬(false = true) from nofun)]
```

More generally:
- `↓reduceIte` works on: `if True`, `if False` (Prop literals)
- `↓reduceIte` fails on: `if (boolExpr = true)` until `= true` is resolved
- After `rw [if_pos h]` or `rw [if_neg h]`, the `if` is fully eliminated

## WF Compatibility: `do`/`guard` vs Explicit `if`/`match`

The termination checker cannot extract guard conditions from `do`
notation. Replace monadic guards with explicit `if`/`match`:

```lean
-- BAD: termination checker can't see the guard
do
  guard (acc.length > 0)
  ...

-- GOOD: guard condition is visible to the termination checker
if acc.length == 0 then none
else ...
```

This was required for `decodeCLSymbols` and `decodeSymbols` WF conversions.

## Fuel-to-WF Migration Checklist

When converting a fuel-based function to well-founded recursion:

### Function Changes
1. Remove the `fuel : Nat` parameter
2. Replace `fuel + 1` pattern matches with actual termination guards
3. Add `termination_by measure` and `decreasing_by` clauses
4. Replace `do`/`guard` with explicit `if h : cond` (dependent if) so
   the termination checker can see the guards

### Proof Changes
1. Replace `induction fuel` with either:
   - `induction args using f.induct` (preferred for complex branching)
   - Same `termination_by` + `decreasing_by` on the theorem (simpler cases)
2. Fuel-independence proofs (`f x (fuel + 1) = some r → ∀ k, f x (fuel + k) = some r`)
   become unnecessary — delete them
3. Replace `simp only [f]` with `unfold f` (WF functions loop under `simp`)
4. Replace `guard`/`by_cases` patterns with `split at h` or `by_cases` + `dif_pos`/`dif_neg`

### Common Pitfalls During Migration
- **Sorry count increases temporarily**: Converting the function breaks
  all downstream proofs. Patch with `sorry` and fix incrementally.
- **`simp only [f]` loops**: The most common mistake. Always use `unfold f`
  or `rw [f.eq_1]` for WF functions.
- **`omega` can't see data invariants**: Use the `dataSize` parameter
  pattern (above) to avoid needing `br.data.size` invariants in `omega`.

## WF Goal Shape: Conjunction with Guard

When proving properties of WF functions using `Nat.strongRecOn` (rather
than `f.induct`), `simp` on the non-final recursive branch may produce
a **conjunction** goal rather than a plain function application:

```lean
⊢ bits'.length < bits.length ∧ decode.go (bits' ++ suffix) acc' = some result
```

This happens because Lean's WF recursion elaboration bundles the
termination proof with the recursive call. The left conjunct is the WF
guard, the right is the actual property.

**Fix:** Supply both parts explicitly:
```lean
exact ⟨hblen, ih bits'.length (hlen ▸ hblen) bits' acc' result rfl hgo⟩
```

**Don't try:** `dif_pos`, `rw`, or `simp only` with the guard hypothesis —
the conjunction is not a `dite`, it's already been simplified past that.

See `Zip/Spec/DeflateSuffix.lean:498` (`decode_go_suffix` proof).

## Multi-State While Loops (decompressBlocks Pattern)

Some `while` loops thread many state variables through iterations:

```lean
-- decompressBlocks threads 5 variables:
while !done do
  let (hdr, off') ← parseBlockHeader data off
  let (blockOutput, off'') ← decodeBlock data off' hdr prevHuffTree prevFseTables
  output := output ++ blockOutput
  prevHuffTree := updatedTree
  prevFseTables := updatedTables
  offsetHistory := updatedHistory
  off := off''
  done := hdr.isLastBlock
```

### WF refactoring pattern

Convert `while !done` to explicit recursion with all state as parameters:

```lean
def decompressBlocksWF (data : ByteArray) (off : Nat)
    (output : ByteArray) (prevHuffTree : Option HuffmanTree)
    (prevFseTables : Option FseTables) (offsetHistory : OffsetHistory) :
    Except Error (ByteArray × Nat) :=
  let hdr ← parseBlockHeader data off
  let (blockOutput, off', tree', tables', hist') ← decodeBlock ...
  if hdr.isLastBlock then
    .ok (output ++ blockOutput, off')
  else
    decompressBlocksWF data off' (output ++ blockOutput) tree' tables' hist'
termination_by data.size - off
```

### Key considerations

1. **Termination measure**: Usually `data.size - off` where `off`
   advances each iteration. Need a lemma that `parseBlockHeader` and
   `decodeBlock` advance `off` (i.e., `off' > off`).

2. **Implicit termination**: The original `while` loop terminates because
   `hdr.isLastBlock` is eventually true OR `off` exceeds `data.size`. For
   WF recursion, only `data.size - off` decreasing is needed (the
   `isLastBlock` case is the base case, not a termination argument).

3. **Error short-circuits**: In Except monad, errors terminate the
   recursion naturally. Only the `.ok` path needs to show decreasing.

4. **State bundling**: If the state tuple is large (5+ fields), consider
   a structure:
   ```lean
   structure DecompressState where
     output : ByteArray
     huffTree : Option HuffmanTree
     fseTables : Option FseTables
     offsetHistory : OffsetHistory
   ```
   This keeps the function signature manageable and makes `f.induct`
   cases more readable.

### When NOT to refactor

Not every `while` loop needs WF conversion. Only refactor when:
- A spec theorem needs to unfold the loop body (e.g., proving output
  size equals content size through block accumulation)
- The loop invariant involves state that changes each iteration

If the only spec theorem is about the function's return type or error
conditions (not loop-internal state), leave the `while` loop and prove
the theorem by treating the function as opaque.

## Cross-References

- **Fuel-based patterns**: `lean-fuel-induction` skill (for functions still using fuel)
- **Roundtrip proofs with WF functions**: `lean-roundtrip-proofs` skill
- **`↓reduceIte` and Bool/Prop**: `lean-simp-tactics` skill
- **Monad unfolding after `unfold`**: `lean-monad-proofs` skill
  (use `dsimp only [bind, Except.bind]` after `unfold` on recursive functions)
