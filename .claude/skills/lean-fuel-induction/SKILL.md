---
name: lean-fuel-induction
description: Use when Lean 4 proofs involve fuel-based recursion, proving fuel independence, loop invariants, copyLoop-style patterns, or suffix/append extension lemmas.
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
