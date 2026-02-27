---
name: lean-fuel-induction
description: Use when Lean 4 proofs involve fuel-based recursion, proving fuel independence, loop invariants, copyLoop-style patterns, suffix/append extension lemmas, or maxRecDepth/maxHeartbeats tuning.
allowed-tools: Read, Bash, Grep
---

# Lean 4 Fuel Induction and Loop Invariant Patterns

## Avoid `forIn` on `Range` in Proofs

`forIn [:n]` uses `Std.Legacy.Range.forIn'` with a well-founded recursion `loop✝`
that CANNOT be unfolded by name. `with_unfolding_all rfl` only works for concrete
values (`:= [:0]`, `[:1]`) not symbolic `n`.

If you need to prove properties of a `for i in [:n]` loop, replace it with explicit
recursion (see `copyLoop` in `Inflate.lean`).

## Fuel Independence Proof Pattern

For fuel-based recursive functions:
`f x (fuel + 1) = some result → ∀ k, f x (fuel + k) = some result`

Use induction on fuel with:
1. `conv => lhs; rw [show n+1+k = (n+k)+1 from by omega]` before `unfold f at h ⊢`
   so both sides unfold at the same successor level
2. `cases` on each non-recursive operation
3. `ih` for recursive calls

For `if` reduction in `h`, use `rw [if_pos/if_neg]` NOT `simp [cond]` — simp
over-simplifies (strips `some`/`pure` wrappers).

For `guard` in do-blocks, use `by_cases` on the condition then:
```lean
simp only [guard, hcond, ↓reduceIte]
```
The guard uses `Alternative.guard`, NOT `Option.guard`.

## Loop Invariant Proof Pattern

For recursive functions like `copyLoop buf start distance k length`, prove a
generalized invariant by well-founded induction carrying the full buffer state:
1. State the invariant relating `buf` to the original `output`
2. Base case: `k = length`, `copyLoop` returns `buf`, use hypothesis
3. Inductive step: show `buf.push x` satisfies the invariant for `k+1`

Key lemmas:
- `push_getElem_lt` — push preserves earlier elements
- `push_data_toList` — `(buf.push b).data.toList = buf.data.toList ++ [b]`
- `List.ofFn_succ_last` — snoc decomposition of `List.ofFn`

## Combined Invariant Lemma Pattern for BitReader/State Operations

When proving that a chain of operations on a stateful type (like `BitReader`) preserves
multiple properties (data equality, position bound, position invariant), bundle all into
a single `∧` return rather than proving each separately:

```lean
private theorem op_inv (br br' : BitReader) ...
    (h : op br = .ok (result, br'))
    (hpos : br.bitOff = 0 ∨ br.pos < br.data.size)
    (hple : br.pos ≤ br.data.size) :
    br'.data = br.data ∧
    (br'.bitOff = 0 ∨ br'.pos < br'.data.size) ∧
    br'.pos ≤ br'.data.size
```

Chain with: `have ⟨hd₁, hpos₁, hple₁⟩ := op_inv ...`
then `exact ⟨hd'.trans hd₁, hpos', hple'⟩`.

This avoids 3× boilerplate and makes chaining across multiple operations clean.
See `GzipCorrect.lean` for examples (`readBit_inv` through `decode_inv`).

### Threading Invariants Through Long Call Chains

For proofs like `inflateLoop_endPos_le` that must thread invariants through
5+ sequential monadic operations, the pattern is:

```lean
-- Each operation produces updated state + invariants
have ⟨hd₁, hpos₁, hple₁⟩ := readBits_inv br br₁ _ _ h_readBits hpos hple
have ⟨hd₂, hpos₂, hple₂⟩ := decode_inv tree br₁ br₂ _ h_decode hpos₁ hple₁
have ⟨hd₃, hpos₃, hple₃⟩ := readBits_inv br₂ br₃ _ _ h_readBits₂ hpos₂ hple₂
-- ...
-- At the end, compose data equalities:
exact ⟨hd_final.trans (hd₃.trans (hd₂.trans hd₁)), hpos_final, hple_final⟩
```

**Key points:**
- Each `_inv` lemma takes the **output invariants** from the previous operation as input
- Data equality chains compose right-to-left via `.trans`: `hd₃.trans (hd₂.trans hd₁)`
  proves `br₃.data = br.data` from `br₃.data = br₂.data`, `br₂.data = br₁.data`,
  `br₁.data = br.data`
- For recursive calls (induction step), pass the final state's invariants to `ih`,
  then `.trans` the recursive result with the accumulated chain

### Deeply Nested Multi-Path Case Splits

When a function branches based on a decoded symbol (e.g., literal vs end-of-block vs
length-distance), the invariant proof must cover all paths:

```lean
split at h
· -- Path 1 (e.g., literal byte)
  have ⟨hd', hp', hl'⟩ := ih br₁ _ h hpos₁ hple₁
  exact ⟨hd'.trans hd₁, hp', hl'⟩
· split at h
  · -- Path 2 (e.g., end of block) — state unchanged
    simp only [Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨_, rfl⟩ := h
    exact ⟨hd₁, hpos₁, hple₁⟩
  · -- Path 3 (e.g., length+distance) — chain through more operations
    -- ... extract sub-operations, chain their _inv results ...
    exact ⟨hd'.trans (hd₄.trans (hd₃.trans (hd₂.trans hd₁))), hp', hl'⟩
```

The error path for each sub-operation is handled by `simp [h_op] at h` which
derives a contradiction from `.error = .ok`.

## `termination_by` Proofs vs `Nat.strongRecOn`

When proving properties about a function defined with `termination_by expr`,
prefer defining the theorem with the same `termination_by` + `decreasing_by`
and making recursive calls directly, over using `Nat.strongRecOn`:

```lean
-- Good: matches the function's own recursion structure
private theorem f_property (data : ByteArray) (pos : Nat) (hpos : pos ≤ data.size) :
    P (f data pos) := by
  by_cases h : base_case
  · ... -- base case
  · have h_rec := f_property data (pos + step) (by omega)  -- recursive call
    ...
  termination_by data.size - pos
  decreasing_by omega
```

`Nat.strongRecOn` creates an induction variable `n` separate from the actual
measure `data.size - pos`. This causes two problems:
1. The induction hypothesis involves elaborating the full recursive term,
   hitting `maxRecDepth` on complex functions
2. The final arithmetic goals have `n` instead of `data.size - pos`, requiring
   explicit `subst` or `have : n = data.size - pos`

Direct `termination_by` avoids both issues since `data.size - pos` stays
concrete throughout the proof.

## Suffix/Append Proofs vs Fuel-Independence Proofs

In fuel-independence proofs, `simp only [hds] at h ⊢` processes both hypothesis
and goal simultaneously (same function call in both).

In suffix/append proofs, `h` has `f bits` while `⊢` has `f (bits ++ suffix)` —
`simp only [hds]` won't match the goal.

**Pattern:**
1. `simp only [hds, bind, Option.bind] at h` — process the hypothesis
2. `rw [f_append ...] at ⊢` — transform the goal
3. `simp only [bind, Option.bind]` — reduce `Option.bind (some (...)) (fun ...)` in goal

For `if` branches appearing in both sides, use `by_cases hcond : condition`
then `rw [if_pos/if_neg hcond] at h ⊢`.

Note: `split at h ⊢` (multiple targets) is NOT supported — use `by_cases` instead.

## Except Suffix Invariance: When `dsimp`/`simp` Is Unnecessary

In Except monad suffix proofs (`f (brAppend br suffix) = ... brAppend br' suffix`),
two common false patterns waste build iterations:

1. **After `cases hx : pure_func args | ok val =>`**: The `cases` already
   reduces the goal's `match` for the `.ok` branch. Do NOT `simp only [hx] at ⊢`
   — only apply to `h`. Use `simp only [hx] at h; dsimp only [] at h ⊢` if
   needed, or just `simp only [hx] at h`.

2. **After `rw [if_neg hcond] at h ⊢`**: The `if` expression is fully reduced.
   A subsequent `simp only [pure, Except.pure] at h ⊢` or `dsimp only [] at h ⊢`
   often makes no progress. Only add these if the goal still contains unreduced
   `pure`/`Except.pure` wrappers — check by building first without them.

**Rule of thumb**: Start minimal (just `rw [if_neg hcond] at h ⊢` then the next
operation), add `dsimp`/`simp` only when the build tells you the goal isn't reduced.

## `maxRecDepth` and `maxHeartbeats` Reduction

After getting proofs to work, reduce `maxRecDepth` and `maxHeartbeats` to the
minimum needed. This speeds up compilation and catches unnecessary unfolding.

**Protocol:**
1. Start with whatever value makes the proof work (e.g., 4096 / 4,000,000)
2. Try halving: 2048 / 2,000,000
3. Table correspondence lemmas (non-recursive `simp` chains) often work at 512
4. Non-recursive proofs may not need any `set_option` at all

**Common values by proof type:**
- Recursive monadic chain (5+ operations): `maxRecDepth 2048` or `4096`
- Single unfold + case split: `maxRecDepth 512` or default
- Pure `simp` / `omega` proofs: no `set_option` needed

Always test by removing the `set_option` entirely first — it may no longer be
needed after proof cleanup.

## Single-Step Unfolding of WF-Recursive Definitions

When proving properties about a well-founded recursive function `f`, you often
need to unfold exactly one level of `f` in the goal without recursively unfolding
all occurrences.

**Problem:** `unfold f` and `delta f` unfold ALL occurrences of `f`, including
recursive calls in the body. For recursive functions like `encodeStored`, this
produces enormous goals or infinite unfolding. `simp only [f, ...]` loops for
the same reason. `conv => unfold f` is invalid inside `conv` blocks.

**Solution:** Use `rw [f.eq_1]` — Lean 4 auto-generates an equation lemma
`f.eq_1` for every definition. It rewrites exactly one application of `f`.

```lean
-- BAD: unfolds encodeStored everywhere, including recursive calls
unfold encodeStored

-- BAD: loops because encodeStored appears in its own body
simp only [encodeStored, ...]

-- GOOD: rewrites exactly one occurrence
rw [encodeStored.eq_1]
```

**When to use a standalone lemma:** If `rw [f.eq_1]` produces a goal too large
to work with directly (many `if`/`match` branches), prove a specialized lemma
that unfolds `f` under specific conditions:

```lean
private theorem f_case2 (xs : List α) (h : ¬(xs.length ≤ N)) :
    f xs = ... body for this case ... := by
  rw [f.eq_1]
  simp only [h, ↓reduceIte, ...]
```

Then `rw [f_case2 _ h]` in the main proof. This was essential for
`encodeStored_non_final` where `unfold encodeStored` was unusable.

**Also beware `let` bindings:** If `f` uses `let x := ...; body`, trying to
rewrite with `← f` to fold back won't work because `rw` can't match through
`let` bindings. Use a standalone lemma instead.

## Cross-Reference: Roundtrip Proofs

For suffix invariance chains (_append lemmas), goR (decode-with-remaining),
and accumulator equivalence patterns, see the `lean-roundtrip-proofs` skill.
