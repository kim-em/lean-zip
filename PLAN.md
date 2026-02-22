# Current Plan

<!-- Rewritten at the start of each work session. -->
<!-- If a session ends with unchecked items, the next session continues here. -->

## Status: In progress

## Session type: implementation (next)

## Goal: Prove copyLoop_eq_ofFn and work toward inflate_correct

### Steps

1. [x] Fix spec bug: pass `acc` to `resolveLZ77` for cross-block back-references
2. [x] State `decodeHuffman_correct`
3. [x] Prove literal case (sym < 256)
4. [x] Prove end-of-block case (sym == 256)
5. [x] Make native tables accessible (lengthBase, etc. now public)
6. [x] Prove table correspondence lemmas
7. [ ] Prove copy loop ↔ List.ofFn (`copyLoop_eq_ofFn`)
8. [x] Complete length/distance case (sym > 256)
9. [ ] Work on inflate_correct loop correspondence

### copyLoop_eq_ofFn

The native `for i in [:length] do out := out.push out[start + (i % distance)]!`
must equal the spec's `List.ofFn fun i => acc[start + (i.val % dist)]!`.

Key insight: all reads are within the original buffer range
(`start + (i % distance) < output.size`), so the growing buffer
doesn't affect read values.

Approach: induction on `length` with loop invariant:
- After `k` iterations, `out = output ++ List.ofFn (fun i : Fin k => ...)`
- At each step, the read `out[start + (k % distance)]!` equals
  `output[start + (k % distance)]!` because `start + (k % distance) < output.size`

### Architecture of remaining decomposition

```
inflate_correct (sorry)
  ├── decodeStored_correct (DONE)
  ├── decodeHuffman_correct (DONE, modulo copyLoop_eq_ofFn)
  │   ├── huffTree_decode_correct (DONE)
  │   ├── literal case (DONE)
  │   ├── end-of-block case (DONE)
  │   └── length/distance case (DONE)
  │       └── copyLoop_eq_ofFn (sorry — standalone lemma)
  └── loop correspondence (for → fuel)
```

### Proof patterns for getElem?/getElem!

- `getElem?_pos` needs explicit container (not `_`) for type class synthesis
- `getElem?_pos` gives `c[i]? = some c[i]`; need `getElem!_pos` for `c[i]!`
- Pattern: `rw [getElem!_pos c i h]; exact getElem?_pos c i h`
- `spec_distBase_pos ⟨n, h⟩` creates Fin coercion mismatch in omega;
  normalize with explicit `have` annotation
- `(n == m) = false`: use `cases heq : n == m <;> simp_all [beq_iff_eq]`
