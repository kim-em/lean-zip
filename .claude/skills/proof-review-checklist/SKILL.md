---
name: proof-review-checklist
description: Use when reviewing Lean proof quality, cleaning up proofs after getting them to work, or performing a review session on a proof file. Also use when the review command targets a Lean file.
allowed-tools: Read, Bash, Grep, Glob
---

# Proof Review Checklist

Mechanical cleanup steps for Lean proof quality reviews. Follow in order, one file at a time, building after each batch of changes.

Bare `simp`/`simp_all` elimination is largely done codebase-wide; new files still need it. With those clean, prioritize: dead `have` bindings, single-use private theorems, proof compression (`grind`/`<;>`/macros/helpers), and `sorry` elimination.

## Phase 0: Verify Issue Accuracy

Before starting, verify the issue's claimed counts against the actual master state — issue descriptions go stale when overlapping PRs touch the same files.

```bash
# Bare simp (excludes simp only, simp_all, simp?, simp_wf, dsimp, etc.)
grep -n 'simp\b' File.lean | grep -v 'simp only\|simp_all\|simp?\|simp_wf\|dsimp\|simp_rfl\|simp (config'
# Bare simpa — uses the full simp database too; the simp\b grep misses it
grep -n 'simpa\b' File.lean | grep -v 'simpa only\|simpa?'
```

If the real count differs sharply from the issue (e.g. issue says 61, master has 0), the file was already cleaned. `coordination skip` and move on.

## Phase 1: Mechanical Cleanup (always safe)

- **Merge consecutive `rw`**: `rw [ha] at h; rw [hb] at h` → `rw [ha, hb] at h`.
- **Merge consecutive `simp only`** (same target only): `simp only [ha] at h; simp only [hb] at h` → `simp only [ha, hb] at h`. Caveat: `simp only` applies all lemmas simultaneously — if the first call creates redexes the second depends on, merging changes the result. Build after merging.
- **Remove dead `have` bindings**: but `omega`/`simp` read the whole local context implicitly, so a "dead" `have` may be feeding them. Build after each removal.
- **Simplify `obtain`**: `obtain ⟨a, b⟩ := h; rw [a]; rw [b]` → `obtain ⟨rfl, rfl⟩ := h`.
- **Extract lemmas (≥3 rule)**: extract only when the pattern appears 3+ times, or 2 times at 6+ lines each. Don't extract short patterns, parameterized-differently sites, or clear inline sequences. Use `private theorem`/`private lemma`.

## Phase 2: Bare `simp` → `simp only`

`simp [X]` is NOT `simp only [X]` (bare uses the whole `@[simp]` database plus `X`). Never mechanically search-and-replace.

**Batch-then-apply** (the key efficiency move for files with 10+ bare simps):
1. Convert ALL bare `simp` to `simp?` at once, build ONCE — yields every `Try this:` suggestion in one pass.
2. Collect the suggested `simp only [...]` replacements.
3. Apply 3-5 at a time, building after each batch (suggestions are computed independently, so some fail in combination).

This turns a 20-bare-simp file from ~20 build cycles into 2-3.

**Per-simp decision tree:**

1. **`simp?`** → use the `Try this:` `simp only [...]` if it works.
2. **`simp only []`** (empty list) for match/iota reduction (constructor scrutinee, after `split`/`match` chains, or when the lone arg is flagged unused). **`dsimp only`** for definitional reductions: `letFun`, beta, `bind`/`Option.bind` with known scrutinee. Prefer `dsimp only` when `simp only []` only reduces let-bindings/projections.
3. **Targeted replacement** by intent:

| Pattern | Replacement |
|---------|-------------|
| `simp at h` closing `error = ok` / `none = some` | `exact nomatch h` |
| `simp [hx]` then contradiction | `exact nomatch (hx ▸ h)` or two-step `simp only [hx] at h; exact nomatch h` |
| Option case `\| none => simp [hvar] at hspec` | `\| none => exact nomatch (hvar ▸ hspec)` |
| Except case `\| error e => simp [hvar] at h` | `\| error e => exact nomatch (hvar ▸ h)` |
| `nomatch (▸)` hits `maxRecDepth` after unfolding a big def (e.g. `inflateRaw`) | Keep two-step `simp only [h] at h; exact absurd h nofun` |
| `simp at hmem` closing `x ∈ []` | `exact nomatch hmem` (NOT `List.not_mem_nil` — its type is `False`, not `¬(x ∈ [])`) |
| `simp at h` closing `[].length ≥ 2` | `simp only [List.length_nil] at h; omega` (omega can't reduce `[].length`; use `List.length_cons` for `[_]`) |
| `simp [bind, Option.bind]` | `dsimp only [bind, Option.bind]` |
| `simp [hx, bind, Option.bind]` | `rw [hx]; dsimp only [bind, Option.bind]` |
| `simp [Prod.mk.injEq]` | `simp only [Except.ok.injEq, Prod.mk.injEq]` |
| `simp; omega` (array size) | `rw [Array.size_set!]; omega` or `rw [Array.size_replicate]; omega` |
| `simp at h` (negated comparison) | `simp only [ge_iff_le, Nat.not_le] at h` or `simp only [gt_iff_lt, Nat.not_lt] at h` |
| `simp_all` (beq→eq + close) | `simp only [beq_iff_eq] at h; exact h` |
| `by simp` (struct field = literal) | `by show <literal_eq>; omega`, `Or.inl rfl`, or `rfl` |
| `simp [Spec.readBitsLSB, ...]` (Option do) | `simp only [Spec.readBitsLSB, ..., Option.pure_def, Option.bind_eq_bind, Option.bind_some]` |
| `simp [hpos]` with `getElem!` | `simp only [getElem!_pos, hpos, ...]` — bridges `data[i]!` to `data[i]` |
| `simp` after `split` on Bool `if` | `split <;> rfl` |
| `simp at h` (double negation) | `exact Decidable.of_not_not h` or `simp only [not_not] at h` |
| `List.reduceReplicate` + `length_cons` + `length_nil` chain | `List.length_replicate` |

4. **Accept with comment** if 1-3 fail — e.g. `-- bare simp: N-level Option.bind chain`, `-- bare simp: concrete bit computation`, `-- bare simp: BitVec normalization`.

**`simp?` daggers**: if a suggestion contains `✝` names (e.g. `UInt32.reduceEq✝`) it's unparseable — use `grind` instead.

## Phase 2a: Bare `simpa`

`simpa` = `simp` + `assumption`. Convert via `simpa?` → `simpa only [...]`. `simpa only []` (empty) is valid structural reduction + assumption — don't flag it.

## Phase 2b: `simp_all`

Powerful (rewrites all hypotheses + goal) but fragile. Convert via `simp_all?`.

| `simp_all` usage | Replacement |
|------------------|-------------|
| Option/Prod destructuring | `simp_all only [Option.some.injEq, Prod.mk.injEq]` |
| after `beq` hypothesis | `simp only [beq_iff_eq] at *; exact h` or `simp_all only [beq_iff_eq]` |
| termination proof | `simp_all only [<specific_lemma>]; omega` |
| Bool→Prop `(x == 0) = false` | `have hne := beq_eq_false_iff_ne.mpr hx0` (hx0 : x ≠ 0) — no simp-db dependency |
| reducing known `if` branch | `rw [if_pos h]` / `rw [if_neg h] at hsize` |
| `simp_all [beq_iff_eq]` for arithmetic contradiction | `simp only [beq_iff_eq] at *; omega` |

Injection kit: `Option.some.injEq`, `Prod.mk.injEq`, `Except.ok.injEq` (plus `obtain ⟨rfl, rfl⟩ := h`) replace most monadic `simp_all`.

Resistance ladder: `simp_all?` → `grind` (handles the same hyp-rewrite + case-split class via a different mechanism) → `simp only [...] at *; omega` / per-hypothesis → accept `simp_all only [...]` best-effort.

## Phase 3: Proof Compression

Shorten proofs without changing statements.

### `grind` for deeply nested monadic case-splitting
Use when a proof needs 4+ nested `split at h` over monadic error/ok branches (3+ sequential `bind`s). Do NOT use where `omega`, `simp only`, or one `split` suffices — it's a sledgehammer.

### Tactic chaining `<;>` and `all_goals`
```lean
split at h; next => exact nomatch h   -- collapse per-branch error closers
all_goals omega                        -- one closer for many goals
```

### `repeat (first | closer | split)` — highest-impact pattern
Replaces arbitrarily deep nested `split` blocks where branches share a closer. `repeat` works on the first goal: `first` tries the closer (closes goal → next goal) else `split` generates sub-goals and `repeat` continues.

```lean
repeat (first | exact ⟨_, _, rfl, rfl, rfl⟩ | split)            -- existential witnesses
repeat (first | decide | split)                                  -- decidable goals
repeat (first | contradiction | (simp only [...] at hsize; omega) | (split at hres))
repeat (first | exact ⟨_, rfl⟩ | split)                          -- constructor existential
```

**Ordering rule**: closer BEFORE `split`; most permissive closer last. **`nomatch` must come LAST** — it raises a *hard error* (not a tactic failure) on satisfiable types like `Except.ok x = Except.ok y`, and `first` cannot catch hard errors.

```lean
-- WRONG: nomatch's hard error blocks the obtain branch
split at h <;> first | exact nomatch h | (obtain ⟨rfl, rfl⟩ := h; rfl)
-- RIGHT: gracefully-failing pattern first, nomatch as fallback
split at h <;> first | (obtain ⟨rfl, rfl⟩ := h; rfl) | exact nomatch h
```

### `List.forall_mem_cons` for `∀ t ∈ cons, P` membership
When `intro t ht; cases ht with | head => …headProof… | tail _ h => …IH…` repeats across `split` branches (identical `tail` arm), collapse each to:
```lean
exact List.forall_mem_cons.2 ⟨headProof, recursiveCall …⟩
```
`List.forall_mem_cons : (∀ x ∈ a :: l, p x) ↔ p a ∧ ∀ x ∈ l, p x`. Idiomatic for matcher-family `∀ t ∈ tokens, encodable t` proofs.

### Local tactic macros for repeated patterns (3+ uses)
```lean
set_option hygiene false in
local macro "unfold_except" : tactic =>
  `(tactic| simp only [bind, Except.bind, pure, Except.pure] at h)
```
`set_option hygiene false` lets the macro capture surrounding names by name (e.g. `h`, or `bfinal`/`br'`/`out'`/`ih` destructured by `obtain` in the enclosing proof). Always scope `local`. Inside `` `(tactic| …) `` quotations the `·` focus dot does NOT parse — use `next =>` and wrap the whole body in parens:
```lean
set_option hygiene false in
local macro "my_tactic" : tactic =>
  `(tactic| (
    by_cases h : condition
    next => tactic_for_true
    next => tactic_for_false))
```

### Helper lemma extraction
When 3+ proofs share the same monadic unfold → split errors → extract fact pattern, hoist a `private theorem foo_elim (h : foo x = .ok (a, b)) : subCallA x = .ok r ∧ … := by …` once; each downstream proof shrinks to 2-3 lines.

### Concise compressions
- `obtain ⟨hval, hbr'⟩ := h; subst hbr'; constructor · exact hval · rfl` → `obtain ⟨hval, hbr'⟩ := h; subst hbr'; exact ⟨hval, rfl⟩`
- Multi-step injection chains → single expression, e.g. `rw [(Prod.mk.inj (Option.some.inj (h₁.symm.trans h₂))).2]; exact hfinal`
- Drop redundant `show T from h` wrappers after `simp only` unfolds let-bindings (when `h : T` already).

### Dead / duplicate code
```bash
grep -n 'private theorem\|private def' File.lean   # then grep each name for other uses
grep -n 'theorem TheoremName' File.lean            # duplicate decls (parallel agents) break the build
```
Remove unreferenced private definitions and unnecessary `termination_by`/`decreasing_by` (only after verifying the build).

### Large block deletion (50+ lines)
Don't use Edit (exact-match is error-prone over large spans). Use:
```bash
head -n N File.lean > /tmp/F.lean && mv /tmp/F.lean File.lean   # tail deletion
sed 'M,Nd'  File.lean > /tmp/F.lean && mv /tmp/F.lean File.lean   # middle deletion
```
Verify with `wc -l` and `tail -5`.

## Phase 4: Type-bridging `have`s that look dead but aren't

These are intentional and must NOT be removed:
- **UInt8/UInt-to-Nat**: `have hlen_pos_nat : sym.len.toNat > 0 := …` — `omega` can't reduce a UInt8 comparison; the `.toNat` version is what it needs.
- **`brAppend` bitPos equality**: `have : (brAppend br suffix).bitPos = br.bitPos := rfl` — `omega` can't see through `bitPos` (a `def`) that `brAppend` (an `abbrev`) preserves `pos`/`bitOff`.
- **`show ...; omega` for structure projections**: `omega` can't reduce `(BitReader.mk data startPos 0).bitOff`; narrow first with `show 0 < 8; omega`. Do NOT reduce to plain `by omega`.

## Phase 5: Linter Compliance

- **Unused simp args** (`bind`, `Option.bind`, `Except.bind`, `letFun` contribute only via dsimp): use the `rw + dsimp` pattern (see `lean-monad-proofs`).
- **`↓reduceIte` flagged**: after `simp only [hf]`, iota handles `if true/false`; drop it.
- **`Option.some.injEq` flagged**: replace `simp only [Option.some.injEq]` with `obtain rfl := Option.some.inj h`.

## Phase 6: Verification

1. `lake build Module.Name`.
2. Re-run the Phase 0 greps; compare counts.
3. Verify no `sorry` introduced and no `maxRecDepth` increase (regression signal).
4. If the PR changes a public-API signature default literal (`max…Size := N`), add an `example … rfl` probe by the docstring pinning the literal — silent on success, loud on drift.

## Phase 7: Commit

One commit per file, prefix `refactor:`, with metrics in the body:
```
refactor: replace bare simp with simp only in FileName.lean

Bare simp: 45 → 12 (73% reduction)
Remaining 12: 8 Option.bind chains, 2 readBitsLSB, 2 BitVec normalizations
```
