---
name: lean-roundtrip-proofs
description: Use when proving encode/decode roundtrip theorems, suffix invariance (_append lemmas), goR (decode-with-remaining) patterns, padding extraction, or composing per-level roundtrip proofs into a unified theorem.
allowed-tools: Read, Bash, Grep
---

# Lean 4 Roundtrip Proof Patterns

## Suffix Invariance (_append Lemmas)

Suffix invariance proves that appending extra bits to decoder input doesn't
affect the decoded result — the decoder processes only its content and leaves
trailing bits untouched.

### Lemma Shape

Every `_append` lemma follows this template:

```lean
theorem f_append (bits suffix : List Bool) (result : T) (rest : List Bool)
    (h : f bits = some (result, rest)) :
    f (bits ++ suffix) = some (result, rest ++ suffix)
```

**Hypothesis**: `f` succeeds on `bits`, consuming them down to `rest`.
**Goal**: `f` succeeds on `bits ++ suffix`, leaving `rest ++ suffix`.

### Building the Chain

Suffix invariance composes bottom-up. Each layer's proof uses the layer below:

1. **Bit-level**: `readBitsLSB_append` — induction on bit count, case-split on list
2. **Decoder-level**: `decodeStored_append`, `decodeLitLen_append`, `decodeSymbols_append`
   — use `readBitsLSB_append` + Huffman decode invariance
3. **Table-level**: `decodeDynamicTables_append` — chains multiple decoder-level appends
4. **Block-level**: `decode_go_suffix` — case-splits on block type, applies per-type append

### Proof Pattern

```lean
theorem f_append (bits suffix : List Bool) ... :
    f (bits ++ suffix) = some (result, rest ++ suffix) := by
  -- Induction on fuel or structure
  induction n generalizing bits result rest with
  | zero => simp_all [f]
  | succ k ih =>
    -- Unfold one layer
    unfold f at h ⊢
    -- Case-split on sub-operations
    cases hx : subOp bits with
    | none => simp [hx] at h
    | some p =>
      obtain ⟨val, rem⟩ := p
      -- Apply lower-level _append to transform goal
      rw [subOp_append bits suffix val rem hx]
      -- Reduce monadic bind
      dsimp only [bind, Except.bind]      -- or Option.bind
      simp only [hx] at h
      -- Recurse or close
      exact ih rem suffix ...
```

### Key Tactics

- **`dsimp only [bind, Except.bind]`** after rewriting with `_append` — reduces
  `match .ok x with ...` without looping (see `lean-monad-proofs` skill)
- **`by_cases hcond : condition`** for `if` branches — apply `rw [if_pos/if_neg]`
  at both `h` and `⊢`
- **Do NOT use `simp [hx] at h ⊢`** simultaneously in suffix proofs — `h` has
  `f bits` while `⊢` has `f (bits ++ suffix)`, so the same simp won't match both

## goR: Decode-With-Remaining Pattern

`goR` is a variant of the decoder's recursive `go` function that returns both
the decoded result AND the remaining (unconsumed) bits.

### When to Use

Use `goR` when you need to prove properties about what the decoder leaves behind
after processing — especially for:
- Padding extraction (how many bits remain after decoding)
- Framing proofs (gzip/zlib wrappers need to know where content ends)
- Byte-alignment proofs (remaining bits must be < 8 for byte boundary)

### Definition Pattern

```lean
def decode.goR (bits : List Bool) (acc : List UInt8) :
    Nat → Option (List UInt8 × List Bool)
  | 0 => none
  | fuel + 1 => do
    let (bfinal, bits) ← readBitsLSB 1 bits
    let (btype, bits) ← readBitsLSB 2 bits
    match btype with
    | 0 =>
      let (bytes, bits) ← decodeStored bits
      let acc := acc ++ bytes
      if bfinal == 1 then return (acc, bits) else decode.goR bits acc fuel
    | 1 => ...  -- same structure, returns (acc, remaining_bits)
    | _ => none
```

### Connection Theorems

Two key theorems connect `goR` to the original `go`:

1. **First projection**: `decode_goR_fst` — `(goR bits acc fuel).map Prod.fst = go bits acc fuel`
2. **Existence**: `decode_goR_exists` — if `go` succeeds, `goR` returns some remaining bits

### Proof Pattern for goR Theorems

```lean
theorem decode_goR_fst ... :
    (goR bits acc fuel).map Prod.fst = go bits acc fuel := by
  induction fuel generalizing bits acc with
  | zero => simp [goR, go]
  | succ n ih =>
    unfold goR go
    -- Case-split on each monadic operation
    cases h1 : readBitsLSB 1 bits with
    | none => simp [h1]
    | some p =>
      simp only [h1, bind, Option.bind]
      -- ... continue matching structure of go ...
      -- Recursive call: exact ih ...
```

## Padding Extraction Pattern

After encoding, the bitstream must be byte-aligned. The padding proof shows
that the encoder's output decomposes as `contentBits ++ padding` where
`padding.length < 8`.

### Structure

```lean
theorem deflateRaw_pad (data : ByteArray) (level : UInt8) :
    ∃ (contentBits padding : List Bool),
      bytesToBits (deflateRaw data level) = contentBits ++ padding ∧
      padding.length < 8 := by
  unfold deflateRaw
  split
  · -- Level 0 (stored): byte-aligned, padding = []
    exact ⟨..., [], ..., by simp⟩
  · split
    · -- Level 1 (fixed Huffman): extract from deflateFixed_spec
      obtain ⟨bits, _, hbytes⟩ := deflateFixed_spec data
      exact ⟨bits, List.replicate ((8 - bits.length % 8) % 8) false,
        hbytes, by simp [List.length_replicate]; omega⟩
    · ...  -- similar for other levels
```

### Key Elements

- **Per-level spec theorems** (e.g., `deflateFixed_spec`) provide the
  `contentBits` and prove `bytesToBits output = contentBits ++ padding`
- **Padding formula**: `List.replicate ((8 - bits.length % 8) % 8) false`
- **Length bound**: `simp [List.length_replicate]; omega` closes the `< 8` goal
- **Stored blocks**: padding is `[]` (empty) since stored blocks are byte-aligned

## Composing Per-Level Roundtrips

The top-level roundtrip theorem composes per-level proofs:

```lean
theorem inflate_deflateRaw (data : ByteArray) (level : UInt8)
    (hsize : data.size < maxSize) :
    inflate (deflateRaw data level) = .ok data := by
  unfold deflateRaw
  split
  · exact inflate_deflateStoredPure data (by omega)
  · split
    · exact inflate_deflateFixedIter data (by omega)
    · split
      · exact inflate_deflateLazy data hsize
      · exact inflate_deflateDynamic data (by omega)
```

### Pattern

1. **Unfold** the top-level encoder
2. **Split** on compression level/strategy
3. **Exact** to per-level roundtrip theorem, passing size bounds via `by omega`

### Per-Level Roundtrip Structure

Each per-level roundtrip follows the same pyramid:

```
encode_spec: encoder produces specific bit structure
    ↓
decode_go_suffix: decoder preserves trailing bits (suffix invariance)
    ↓
goR connection: decoder leaves exactly the padding bits
    ↓
inflate_complete: bit-to-byte alignment → original data recovered
```

## Iterative/Recursive Equivalence (Accumulator Pattern)

When an optimized iterative version uses an accumulator, prove equivalence
with the recursive version.

### Lemma Shape

```lean
theorem iterFunc_eq_recFunc (acc : Array T) (args...) :
    iterFunc args acc = acc ++ (recFunc args).toArray
```

### Proof Pattern

```lean
  induction h : measure using Nat.strongRecOn generalizing pos acc with
  | _ n ih =>
    unfold iterFunc recFunc
    -- Normalize shared helpers (non-recursive = definitionally equal)
    simp only [show @iterHelper = @recHelper from rfl]
    split
    · -- Recursive case: rewrite with IH, then array manipulation
      rw [ih _ (by omega) _ _ rfl]
      rw [List.toArray_cons, ← Array.append_assoc, Array.push_eq_append]
    · -- Base case
      simp
```

### Key Tactics

- **`show @iterHelper = @recHelper from rfl`** — when helper functions are
  definitionally equal (non-recursive), use this as a `simp` lemma to normalize
- **`Array.push_eq_append`** + **`Array.append_assoc`** — for accumulator manipulation
- **`List.toArray_cons`** — converts `(x :: xs).toArray` to `#[x] ++ xs.toArray`
- **Strong induction** on decreasing measure (e.g., `data.size - pos`)

### Composition

Build bottom-up: helper equivalences first, then compose in the main theorem:

```lean
theorem lz77GreedyIter_eq_lz77Greedy (data : ByteArray) (ws : Nat) :
    lz77GreedyIter data ws = lz77Greedy data ws := by
  unfold lz77GreedyIter lz77Greedy
  split
  · rw [trailing_eq]; simp
  · rw [mainLoop_eq]; simp
```
