---
name: lean-simp-tactics
description: Use when simp only fails unexpectedly in Lean 4, or when dealing with Bool vs Prop conditions, filter+lambda, let bindings in omega, linter false positives, or hypothesis normalization mismatches.
allowed-tools: Read, Bash, Grep
---

# Lean 4 `simp` Tactic Pitfalls

## `simp only` won't reduce `List.filter` + anonymous lambdas
`List.filter_cons` unfolds `(a :: l).filter p` to `if p a = true then ...`, but with `p` an anonymous lambda (`(· != 0)`), `p a` stays unreduced — `simp only` can't beta-reduce or evaluate the boolean. Use full `simp`. Also `List.set_cons_zero`/`List.set_cons_succ` are not `@[simp]` — unfold with `simp only` first, then `simp` for the filter/boolean parts.

## `Bool` vs `Prop` in `if` conditions
Check whether the `if` condition is `Bool` or `Prop` before forcing a branch:
- **`Bool`**: `show (cond) = false from by decide`, then `Bool.false_eq_true, ↓reduceIte`.
- **`Prop`**: `show ¬P from by omega`, then `↓reduceIte`.

`>` on `Nat` is a `Prop`, not a `Bool` — don't use `show P = false from by omega` for it.

## `let` bindings are opaque to `omega`
If `hj` mentions `(List.map f xs).length` and you `let pl := List.map f xs`, omega treats `pl.length` and `(List.map f xs).length` as distinct variables. Fix with `change`, which does definitional unfolding so the terms become syntactically identical:
```lean
change j ≥ max 4 (pl.length - tw.length) at hj
```
`simp`/`rfl` equations don't help here.

## `simp` hypothesis must match the post-rewrite form
In `simp only [rewrite_eq, neg_hyp, ↓reduceIte]`, if `rewrite_eq` transforms the condition (e.g. `sym.toUInt16.toNat` → `sym`), then `neg_hyp` must be stated in the *post*-rewrite form (`¬(sym - 257 ≥ ...)`, not the pre-rewrite shape). `simp` applies all rules together, so the hypothesis must match the normalized goal.

## `↓reduceIte` does NOT reduce `false = true`
After `cases b` on a `Bool`, `if b then ...` becomes `if (false = true) then ...`, which elaborates to `@ite _ (false = true) (instDecidableEqBool false true) ...`. `↓reduceIte` does not reduce this because `false = true` is not literally `False`. Use `dsimp` — it reduces `instDecidableEqBool` to `isFalse`/`isTrue` via iota reduction. Decision table:

| Condition form | `↓reduceIte`? | Fix |
|---|---|---|
| `if True/False then …` | Yes | — |
| `if (n > 0) then …` (Prop) | After `rw [if_pos/if_neg h]` | prove `h`, then `rw` |
| `if (false = true) then …` | No | `dsimp` |
| `if (x == y) then …` (Bool) | After `show (x == y) = false` | `Bool.false_eq_true, ↓reduceIte` |
| `if ((8 : Nat) = 0) then …` (concrete numeral Prop) | No | `show ¬((8:Nat)=0) from by omega`, then `↓reduceIte` |

To evaluate `if false = true then X else Y`, use `if_neg Bool.false_ne_true` (not `simp only [ite_false]`, which needs the condition to already be `False`).

## `simp at h` vs `dsimp at h` on `if P then a else none = some b`
`simp at h` deduces `P` must hold (the `else` is `none ≠ some b`) and simplifies to `h : a = some b`. `dsimp at h` cannot — it only does definitional reduction, not propositional `if` reasoning. So use `dsimp at h` only for pure constructor/match reduction; use `simp at h` when the hypothesis has `if P then ... else none` needing propositional resolution.

## `simp [hf]` vs `rw [if_pos/neg hf]` on mismatched length conditions
When the goal's condition is `(bits ++ suffix).length < maxPos` but the hypothesis proves about `bits.length`, `simp [hf]` bridges via `List.length_append` + arithmetic, while `rw [if_pos/neg hf]` / `rw [dif_pos/neg hf]` need exact syntactic match and fail. Don't try to convert `simp [hf]` to `rw` here. (Alternative: a bridge `have` matching the goal's condition exactly, then `rw [if_pos hcond]`.)

## `beq_iff_eq` over-rewrites inside lambdas / `foldl`
`simp only [beq_iff_eq]` rewrites ALL `==` occurrences, including inside a `foldl`/lambda body — turning `(l == b) = true` into `l = b` and breaking downstream goals that expect the Bool form. Scope it with a targeted `have`:
```lean
have hf : ¬((x == b) = true) := by rw [beq_iff_eq]; exact hbeq
simp only [if_neg hf]  -- only the outer if, not the lambda body
```

## `BEq.beq` vs `Nat.beq` — use `eq_of_beq`
A hypothesis `h : (x == 0) = true` from `split` on `if x == 0` is `BEq.beq`, NOT `Nat.beq`, so `Nat.eq_of_beq_eq_true h` fails on a type mismatch. Use `eq_of_beq h` (no namespace) to get `x = 0`. The simp lemma is `beq_iff_eq` (`beq_eq_true_iff_eq` does not exist). For a `¬(w == 0 = true)` guard that omega can't use directly, `revert` it back into the goal first: `revert hw0; simp only [beq_iff_eq]; omega` (matching after `dsimp only []` normalization can otherwise fail).

## Struct field access not reduced by `omega` or `decide`
For `{ data := d, pos := p, bitOff := 0 }.bitOff < 8`, omega doesn't reduce the projection and decide chokes on free variables. Use `show` to reduce the projection manually: `by show 0 < 8; omega`. (And `Or.inl rfl` works directly for `{ … bitOff := 0 }.bitOff = 0 ∨ …` since the projection reduces definitionally.)

## `simp only` vs `subst` for dependent `getElem` rewrites
With `hlenSum : arr[idx] + extraV = len` and `arr[idx]` in the goal, both `rw` and `simp only [hlenSum]` may fail ("Did not find an occurrence") because the `getElem` bound proof in the hypothesis differs from the one in the goal — proof irrelevance doesn't save `simp only` here. Use `subst hlenSum` to eliminate the variable. Common after `rw [getElem!_pos ...]` then `obtain`.

## `Array.getElem_replicate` — Fin vs Nat indexing
`simp only [Array.getElem_replicate]` fails when the index is a `Fin` (from `intro ⟨j, hj⟩`) because the lemma expects `Nat` indexing. Convert first with `show`:
```lean
intro ⟨j, hj⟩
show (Array.replicate n default)[j].field ≤ bound
rw [Array.getElem_replicate]
```

## `Array.size` of a literal under `simp only`
`#[a, b, c]` elaborates as `List.toArray [a, b, c]`. To prove `idx < table.size` with `simp only`, bridge through `List.size_toArray` first:
```lean
simp only [table, List.size_toArray, List.length_cons, List.length_nil] at hidx; omega
```
Include BOTH `List.length_cons` AND `List.length_nil` — without the latter omega sees `[].length` as opaque. Alternative for a standalone bound: `have : table.size = 29 := rfl; omega`.

## Array-literal indexing after `rcases` case split
To prove a property of `arr[code]` for all `code < N` over an RFC lookup table:
```lean
unfold myFunction
simp only [hlt, ↓reduceDIte]
rcases code with _ | _ | _ | _ | _ | _ | _ | _ | _   -- N+1 underscores
all_goals first | omega | rfl
```
After `unfold`, `Array.get` on the literal reduces definitionally per concrete index, so `rfl` closes valid codes and `omega` the impossible one. `simp only [myArray]` alone does NOT reduce the symbolic index, and `decide` over `∀ code : Nat` can't enumerate.

## `omega` cannot handle `2^n` / `1 <<< n`
omega is linear-only. Bridge shifts to powers and supply bounds first:
- `Nat.one_shiftLeft : 1 <<< n = 2 ^ n`
- `Nat.one_le_two_pow : 1 ≤ 2 ^ n`
```lean
have : 1 <<< n ≥ 1 := by rw [Nat.one_shiftLeft]; exact Nat.one_le_two_pow
omega
```
For `X ≤ X + 2^k` from `eA : X + 2^k = Y`, omega *fails* (over ℤ it loses `2^k ≥ 0`). Either establish `have : 1 ≤ 2 ^ k := Nat.one_le_two_pow` before omega, or skip omega: `exact Nat.le.intro eA` / `Nat.le_of_eq eA`.

`simp only [Nat.shiftLeft_eq]` may silently fail to match `<<<` in hypotheses (typeclass chain `HShiftLeft → ShiftLeft → Nat.shiftLeft`). Capture the conversion in a `have` instead:
```lean
have hshift : ∀ k, 1 <<< k = 2 ^ k := fun k => by simp [Nat.shiftLeft_eq]
simp only [hshift] at *
```
To feed omega afterward, establish bounds on `2^(…)` BEFORE `generalize 2 ^ … = p at *` (generalize severs the connection).

## `Nat.testBit` rewrite ordering in bitwise proofs
In `simp only [Nat.testBit_and, Nat.testBit_zero, ...]`, `testBit_zero` may fire first and make `testBit_and` unmatchable. Control order with `rw` first:
```lean
rw [Nat.testBit_and]
simp only [Nat.testBit_zero, heven, Nat.mul_mod_right, Bool.false_and]
```
`simp only` also doesn't always reduce `decide True` / `decide (0 = 1)` — add `decide_true` + `Bool.true_and`, or `show (0:Nat) ≠ 1 from by omega` + `decide_false` + `Bool.false_and`.

## `Nat.mod_eq_sub_mod` for inductive mod proofs
Proving `(n - k) % k = 0` from `n % k = 0` and `n ≥ k` (omega can't reason about `%`): `← Nat.mod_eq_sub_mod hge` rewrites `(n - k) % k` to `n % k`.

## `letFun` / `bind` linter false positives
The linter flags `letFun`, `bind`, `Option.bind`, `Except.bind` as unused in `simp only [...]` because they contribute only via dsimp. Don't suppress with `set_option linter.unusedSimpArgs false`; use the `rw + dsimp` pattern:
```lean
dsimp only at h                                    -- handles letFun
rw [hX] at h; dsimp only [bind, Option.bind] at h ⊢ -- handles bind layers
```

## `have` bindings that look unused but feed `omega`/`simp`
`omega` and `simp` scan the whole local context, so a never-referenced-by-name `have` may be load-bearing (e.g. UInt8/16/32 → Nat bridge hypotheses `have hlen_pos_nat : 0 < x.toNat := hlen`, present because omega works on `Nat` not `UIntN`). Before deleting any `have`, check downstream omega/simp/simp_all and rebuild.

## Bare `simp at h` replacements
- **Constructor discrimination** (`h : Except.error e = Except.ok x` after `split at h`): `simp only` lacks the `reduceCtorEq` simproc, and `contradiction` is unreliable. Use `exact nomatch h`, or one-step `exact nomatch (hrb ▸ h)` when a rewrite makes it an impossible constructor equality. Batch with `split at h; next => exact nomatch h` — NOT `<;> try exact nomatch h` (the "Missing cases" error is elaboration-level, uncaught by `try`).
- **Pair extraction** from `f x = Except.ok (result, bits')`: `simp only [Except.ok.injEq, Prod.mk.injEq] at h; obtain ⟨hval, hrest⟩ := h`. Don't use bare `simp` — it over-simplifies.
- **Match iota reduction** once the scrutinee is a constructor: `simp only []`. (Does NOT reduce `Option.bind none f`.)
- **Double negation** (decidable prop): `exact Decidable.of_not_not h`.
- **Negated comparisons** from a false `if` guard: `simp only [ge_iff_le, Nat.not_le] at h` (gives `a < b`) or `simp only [gt_iff_lt, Nat.not_lt] at h` (gives `a ≤ b`); rebuild to confirm the form.

## `repeat split at h` only processes the first goal
`repeat tac` retries only on the first unsolved goal, so it leaves the second `split` branch unsplit. For chained if-then-else, use a flat sequence: `split at h` / `· handle_case` / `split at h` / `· …` / `handle_last`.

## `simp only []` vs `dsimp only []` to expose an `if` under `let`s
`dsimp only []` zeta-reduces lets so `split` can see an inner `if`. Use `dsimp only []`, NOT `simp only []` — the latter also rewrites the block terms, so a later `rw [show … = … from …]` fails with "did not find pattern". Related gotchas for size-then-emit dispatch:
- `split` fires on the innermost / first-occurring `if`; a nested size condition needs `split <;> split` with the four `exact`s ordered (stored, fixed, stored, dyn).
- Bump `maxRecDepth` (`set_option maxRecDepth 8000 in`) — `split` whnf's the size condition.
- Mark cheap cost-model defs `@[irreducible]` (a fold over `List.range 286` blows maxRecDepth on whnf). Irreducibility blocks elaborator unfolding only; kernel/compiled eval and `decide`/conformance tests are unaffected.

## When bare `simp` is acceptable (leave a justifying comment)
`simp only` genuinely can't replace these — comment and keep:
| Pattern | Comment |
|---|---|
| Option/Except.bind chains >3 levels deep | `-- bare simp: N-level Option.bind chain` |
| Concrete bit computation (`simp [readBitsLSB]` is the eval engine) | `-- bare simp: concrete bit computation` |
| Multi-type BitVec/UInt normalization (`&&&`, shifts, casts) | `-- bare simp: BitVec normalization` |
| `if` bridging `(a ++ b).length` vs `a.length` | `-- bare simp: bridges List.length_append` |

## `split <;> rfl` for symmetric Bool goals
`(if b then x else x) = x`, or both branches of a Bool match/if producing the same result, closes with `split <;> rfl`. If branches differ by more than definitional equality (`x + 0` vs `x`), use `split <;> simp` or `split <;> omega`.

## `simp (config := { decide := true }) only [...]`
Combines `simp only` precision with `decide` evaluation in one step (e.g. rewrite then evaluate a concrete BFINAL flag). Distinct from `simp only [...]; decide`, which only works if `simp only` fully simplifies first.

## ByteArray eta: `⟨⟨result.data.toList⟩⟩ = result` is `rfl`
Structures have eta in Lean 4, so `ByteArray.mk (Array.mk result.data.toList) = result` closes by `rfl` — no `simp`/`ext`/lemmas.

## `simp?` suggests dagger lemmas (`✝`) that won't compile
`simp?` may suggest auto-generated lemmas like `UInt32.reduceBEq✝` (common for UInt `BEq` reduction); the `✝` is not a valid identifier so `simp only [UInt32.reduceBEq✝]` won't compile. Replace with `decide` for concrete BEq, or explicit `cases b` analysis. Arises when converting `cases b <;> simp_all` to `simp only`.

## Unhygienic tactic macro referencing a hypothesis name
To write a macro that uses a fixed hypothesis name `h`:
```lean
-- regular comment, not a docstring
set_option hygiene false in
local macro "unfold_except" : tactic =>
  `(tactic| simp only [bind, Except.bind, pure, Except.pure] at h)
```
Constraints: `set_option hygiene false in` BEFORE `local macro`; OUTSIDE any `namespace` (a `local macro` inside gets a private scoped name call sites can't resolve); a regular comment (not docstring) before the `set_option`. The `$h`/`at $h` splice forms (`scoped macro … h:ident`, `scoped syntax`+`macro_rules`) fail with `h.raw` errors.

## `simp_all only` in `decreasing_by` needs three lemma categories
`simp_all only` doesn't take let-binding names as args. To replace bare `simp_all`, supply all three at once:
1. negated guard normalizers (`ge_iff_le` + `Nat.not_le`, or `gt_iff_lt` + `Nat.not_lt`);
2. structural lemmas for the let-bound expression (e.g. `List.length_cons` for `let acc' := sym :: acc`);
3. the original explicit lemmas.
```lean
decreasing_by all_goals simp_all only [
  List.length_append, List.length_replicate, ge_iff_le, Nat.not_le, List.length_cons]; omega
```
