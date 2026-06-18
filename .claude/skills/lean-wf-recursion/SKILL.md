---
name: lean-wf-recursion
description: Use when Lean 4 proofs involve well-founded recursion, termination_by, f.induct functional induction, unfolding WF functions, or converting fuel-based functions to WF recursion.
allowed-tools: Read, Bash, Grep
---

# Lean 4 Well-Founded Recursion Proof Patterns

## `simp only [f]` loops on WF functions

Never `simp only [f]` for a WF function: simp rewrites `f` inside its own body, which always contains a recursive call to `f`, so it never reaches a fixpoint. Use `unfold f` or `rw [f.eq_1]` instead.

## `unfold f` — default single-level unfold

Exposes guard conditions; follow with `split` to case-analyze the exposed `if`/`match`.

```lean
unfold tokenFreqs.go
split
· -- guard satisfied: i < tokens.size
· -- guard failed
```

`unfold f` expands ALL occurrences (including recursive calls). See `Zip/Spec/DeflateDynamicFreqs.lean`.

## `rw [f.eq_1]` — rewrite exactly one application

Use when `unfold` is too aggressive or when you need it inside `conv`. When `f` matches on constructors, Lean generates `f.eq_1`, `f.eq_2`, ... (one per arm) — pick the one for your case. The `.eq_1` name is not guaranteed to exist.

```lean
rw [kraftSumFrom.eq_1]
exact if_neg (by omega)
```

See `Zip/Spec/HuffmanKraft.lean`.

## Step theorems: unfold only one side of `f a = f b`

`unfold f` expands BOTH sides. Three ways to unfold the LHS only:

1. `rw [f.eq_1]` — only if the equation lemma name exists.
2. `rw [show f args = _ from by unfold f; rfl]` — universally works; unfolds `f` in a local proof, `rfl` closes `body = body`, the result rewrites only the first match.
3. `generalize heq : f b = rhs` to make the RHS opaque, then `unfold f` hits the LHS alone.

After unfolding through guards, residual elaboration differences (`match x with` vs `match x, h with`) close with:

```lean
congr 1
cases x <;> rfl
```

`generalize` form:

```lean
theorem f_step (h1 ...) (h2 ...) : f x₁ = f x₂ := by
  generalize heq : f x₂ = rhs     -- RHS becomes opaque
  unfold f                          -- unfolds LHS only
  simp only [h1, h2, ↓reduceDIte, ↓reduceIte,
    bind, Except.bind, pure, Except.pure, Bool.false_eq_true]
  exact heq
```

Why other approaches fail: `unfold` is not available inside `conv`; `Eq.trans` with a metavariable leaves `?mid` unsynthesized. See `Zip/Spec/Zstd.lean` (`decompressBlocksWF_raw_step`, `_rle_step`) and `Zip/Spec/Deflate.lean` (`decompressBlocksWF` step theorem).

## Standalone case lemma when `rw [f.eq_1]` goal is too big

```lean
private theorem f_case2 (xs : List α) (h : ¬(xs.length ≤ N)) :
    f xs = ... body ... := by
  rw [f.eq_1]
  simp only [h, ↓reduceIte, ...]
```

Then `rw [f_case2 _ h]`. See `encodeStored_non_final` in `Zip/Spec/Deflate.lean`.

## Functional induction with `f.induct`

Every WF function `f` gets an auto-generated `f.induct` whose cases match the recursion. Fails to generate if `f`'s termination proof uses `sorry`.

```lean
induction data using encodeStored.induct generalizing acc with
| case1 data hle => unfold encodeStored; simp only [hle, ↓reduceIte]; ...
| case2 data hgt rest ih => ...
```

- `generalizing acc` for accumulator parameters.
- `ih` is the hypothesis for recursive calls.

Alternative: a theorem with the same `termination_by` + `decreasing_by`. Use `f.induct` for complex branching (no measure duplication); use matching `termination_by` for simple functions (see `lean-fuel-induction`). See `Zip/Spec/Deflate.lean`.

## Termination measures

| Measure | Used for |
|---------|----------|
| `tokens.size - i` | array traversal |
| `xs.length` | list consumption |
| `dataSize * 8 - br.bitPos` | bit-stream decoding |
| `totalCodes - acc.length` | bounded accumulator growth |

### `dataSize` parameter pattern

For bit-stream consumers, pass `br.data.size` as a fixed `dataSize` parameter rather than referencing `br.data.size` directly. `omega` cannot derive `br'.data.size = br.data.size` without invariant lemmas; a fixed parameter avoids the dependency.

```lean
def decodeHuffman (br : BitReader) ... := go br.data.size br output
where go (dataSize : Nat) (br : BitReader) ... :=
  ... go dataSize br₁ ...
  termination_by dataSize * 8 - br.bitPos
```

See `Zip/Native/Inflate.lean`.

## Dependent `if` guards: `dif_pos` / `dif_neg`

WF functions use dependent `if` to bind the termination witness:

```lean
if _h : bits'.length < bits.length then decodeSymbols ... bits' ... else none
```

Select branches in proofs:

```lean
by_cases hlt : bits'.length < bits.length
· simp only [dif_pos hlt] at h ...
· simp only [dif_neg hlt] at h ...
```

Or prove the guard and `rw [dif_pos hlen]`. See `Zip/Spec/DeflateEncode.lean`, `Zip/Spec/DeflateSuffix.lean`.

## `split at h` for `if` in a hypothesis

When a hypothesis contains an `if` from a WF function, `split at h` case-analyzes it directly (replaces the old `guard` + `by_cases`):

```lean
split at ht
· simp at ht; ...   -- guard satisfied
· simp at ht; ...   -- guard failed
```

See `Zip/Spec/LZ77NativeCorrect.lean`.

## `↓reduceIte` fails on `if (false = true)`

`↓reduceIte` reduces `if True/False` (Prop literals) but NOT `if (boolExpr = true)`, which arises when a Bool equality coerces to Prop. Resolve explicitly:

```lean
simp only [if_neg (show ¬(false = true) from nofun)]
```

After `rw [if_pos h]` / `if_neg h` the `if` is fully eliminated.

## WF compatibility: replace `do`/`guard` with explicit `if`/`match`

The termination checker cannot extract guards from `do` notation. Replace:

```lean
-- BAD
do guard (acc.length > 0); ...
-- GOOD
if acc.length == 0 then none else ...
```

Required for `decodeCLSymbols`, `decodeSymbols`.

### `do` early-throw does not bind the negated guard

`if cond then throw ...` (no explicit `else`) in `do` does NOT keep the negated condition in scope through later monadic binds, so later termination proofs cannot reference it. Use a top-level dependent `if`/`else do`:

```lean
-- GOOD: hoff : ¬(data.size ≤ off) stays in scope
def f ... :=
  if hoff : data.size ≤ off then .error "error"
  else do
    ...
    have : data.size - newOff < data.size - off := by omega   -- WORKS
```

Required for `decompressBlocksWF` in `ZstdFrame.lean`.

## Non-advancement guard pattern

Make termination self-contained: guard that a sub-operation advanced, throwing if not. The guard's `else` hypothesis discharges the measure by `omega` — no inline advancement proof, no `decreasing_by`.

```lean
def decompressZstdWF (data : ByteArray) (pos : Nat) (output : ByteArray) :
    Except String ByteArray :=
  if hpos : pos ≥ data.size then return output
  else do
    let (content, afterFrame) ← decompressFrame data pos
    if hadv : afterFrame ≤ pos then throw "frame did not advance position"
    else
      have : data.size - afterFrame < data.size - pos := by omega
      decompressZstdWF data afterFrame (output ++ content)
termination_by data.size - pos
```

Use when: the advancement proof exists but is complex to inline; you want termination independent of that proof; multiple recursive paths each need their own guard. The per-parser `_pos_gt` theorems (`lean-zstd-spec-pattern`) prove the guard never fires, but the WF function does not depend on them. Same pattern: `decompressBlocksWF` (`ZstdFrame.lean`) with `parseBlockHeader` + `decodeBlock`.

### Termination obligations are usually `omega`

The guard pattern produces goals like `h : ¬(afterPos ≤ pos) ⊢ data.size - afterPos < data.size - pos` — pure linear arithmetic. If `omega` fails, the measure has non-linear terms (multiplication/exponentiation) needing auxiliary `have` lemmas to linearize.

## WF goal shape: conjunction with guard

With `Nat.strongRecOn` (not `f.induct`), `simp` on a non-final recursive branch may yield a conjunction (left = WF guard, right = property) rather than a plain application:

```lean
⊢ bits'.length < bits.length ∧ decode.go (bits' ++ suffix) acc' = some result
```

Supply both parts; it is not a `dite`, so `dif_pos`/`rw`/`simp` with the guard will not help:

```lean
exact ⟨hblen, ih bits'.length (hlen ▸ hblen) bits' acc' result rfl hgo⟩
```

See `Zip/Spec/DeflateSuffix.lean` (`decode_go_suffix`).

## Multi-state `while` loops → explicit recursion

A `while !done` loop that threads many state vars (output, prevHuffTree, prevFseTables, offsetHistory, off) converts to recursion with all state as parameters:

```lean
def decompressBlocksWF (data : ByteArray) (off : Nat) (output : ByteArray)
    (prevHuffTree : Option HuffmanTree) (prevFseTables : Option FseTables)
    (offsetHistory : OffsetHistory) : Except Error (ByteArray × Nat) :=
  let hdr ← parseBlockHeader data off
  let (blockOutput, off', tree', tables', hist') ← decodeBlock ...
  if hdr.isLastBlock then .ok (output ++ blockOutput, off')
  else decompressBlocksWF data off' (output ++ blockOutput) tree' tables' hist'
termination_by data.size - off
```

- Measure `data.size - off`; need a lemma that the sub-ops advance `off`.
- `isLastBlock` is the base case, not a termination argument; only `data.size - off` decreasing matters.
- In `Except`, errors short-circuit; only the `.ok` path shows decreasing.
- For 5+ state fields, bundle into a structure to keep the signature and `f.induct` cases readable.

Refactor only when a spec theorem must unfold the loop body or its invariant involves per-iteration state. If the theorem only concerns the return type or error conditions, leave the `while` loop and treat the function as opaque. (Note: `forIn` loops from `while`/`for ... in [:n]` use auto-generated `loop✝` functions that CANNOT be unfolded — refactor to WF recursion early if you need to reason through them.)

## Explicit `match` over `do` for proof targets

`do` desugars to `Bind.bind`, which needs `simp only [bind, Bind.bind, Except.bind]` to unfold — and that often fails after `dite` splits or `let` bindings when the bind is not top-level. Explicit `match` makes `split at h` predictable: each error/ok branch is directly visible.

```lean
-- GOOD: every branch visible
match f1 br with
| .error e => .error e
| .ok (a, br) =>
  if h : cond then
    match f2 br with
    | .error e => .error e
    | .ok (b, br) => ...
  else .error ...
```

Exception: `do` is fine for 1-2 tail-position binds (e.g. `decodeFseSymbolsWF.loop`). For 3+ interleaved states (sequence decoding), use explicit match. After `unfold` on a recursive function, use `dsimp only [bind, Except.bind]` (see `lean-monad-proofs`).

## Fuel-to-WF conversion template

### Phase 1: function

1. **Pick the measure** by recursion structure:
   - counter (`remaining : Nat`) → structural recursion via `match`, no `termination_by`
   - position (`data.size - pos`) → `termination_by` + guard
   - custom → `termination_by` + `decreasing_by`
2. **Remove fuel, add measure**; replace `fuel + 1` matches with real guards.

```lean
-- BEFORE
def decode (fuel : Nat) ... := match fuel with | 0 => .error "out of fuel" | fuel+1 => ...
-- AFTER (counter-based, structural)
def decodeWF (data : ByteArray) (br : BackwardBitReader) (count : Nat) (acc : ByteArray) :=
  match count with
  | 0 => .ok (acc, br)
  | n + 1 => do let (sym, br') ← decodeSymbol br; decodeWF data br' n (acc.push sym)
```

3. **Replace `do`/`guard` with explicit `if`/`match`** when 3+ sequential monadic ops.
4. **Extract a per-iteration helper** if nesting exceeds ~10 levels (the helper may use `do` freely since proofs only unfold the loop structure):

```lean
private def decodeOneStep (...) : Except String (...) := do ...
def decodeWF.loop (tables : Tables) (br : BackwardBitReader) (state remaining : Nat) (acc : Array UInt8) :=
  match remaining with
  | 0 => .ok (acc, br)
  | n + 1 =>
    match decodeOneStep tables br state with
    | .error e => .error e
    | .ok (result, br', stateUpdate) => decodeWF.loop tables br' stateUpdate.newState n (acc.push result)
```

| Nesting | Action |
|---------|--------|
| ≤ 5 | inline |
| 6-10 | extract if proofs get unwieldy |
| > 10 | always extract |

Signs you need extraction: `split at h` yields 4+ unreduced `match`/`if` layers, or the same error-branch dismissal repeats 5+ times.

### Phase 2: size theorem

Induct on the counter; `simp only` to unfold one level; `cases` on sub-ops; `nomatch` for error branches; `omega` to close.

```lean
theorem decodeWF_size {br br'} {count} {acc result}
    (h : decodeWF br count acc = .ok (result, br')) : result.size = acc.size + count := by
  induction count generalizing br acc with
  | zero =>
    simp only [decodeWF, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, _⟩ := h; omega
  | succ n ih =>
    simp only [decodeWF, bind, Except.bind] at h
    cases hsub : subOperation br with
    | error => simp only [hsub] at h; exact nomatch h
    | ok v =>
      obtain ⟨val, br₁⟩ := v
      rw [hsub] at h; dsimp only [Bind.bind, Except.bind] at h
      have := ih h
      simp only [ByteArray.size_push] at this; omega
```

### Phase 3: downstream proof repair

1. Patch everything with `sorry` to get a compiling codebase.
2. Fix one at a time, simplest first (size theorems).
3. Replace `simp only [f]` with `unfold f`.
4. Replace `induction fuel` with `induction count generalizing ...` (or `induction ... using f.induct`).
5. Delete fuel-independence proofs (`f x (fuel+1) = some r → ∀ k, f x (fuel+k) = some r`) — no longer needed.
6. Replace `guard`/`by_cases` with `split at h` or `by_cases` + `dif_pos`/`dif_neg`.
7. `omega` can't see data invariants → use the `dataSize` parameter pattern.

## Cross-references

- `lean-fuel-induction` — functions still using fuel
- `lean-roundtrip-proofs` — roundtrip proofs with WF functions
- `lean-simp-tactics` — `↓reduceIte` and Bool/Prop
- `lean-monad-proofs` — monad unfolding after `unfold` (`dsimp only [bind, Except.bind]`)
- `lean-zstd-spec-pattern` — size/content theorems for WF helpers; position-advancement proofs
- `lean-content-preservation` — content characterization patterns
