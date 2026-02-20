# Current Plan

<!-- Rewritten at the start of each work session. -->
<!-- If a session ends with unchecked items, the next session continues here. -->

## Status: In progress

## Session type: review

## Goal: Deep review of InflateCorrect.lean + resolveLZ77 properties

### Focus areas

- [x] **Proof improvement**: InflateCorrect.lean (new file, first review)
- [ ] **Theorem statement correctness**: All sorry'd theorems
- [ ] **Duplication / code quality**: Cross-file redundancy
- [ ] **Lean idioms**: Simplification opportunities

### Findings and actions

#### Critical: `readBits_toBits` missing hypotheses

The sorry'd theorem at InflateCorrect.lean:184 is unprovable as stated.
Two missing hypotheses:

1. `hwf : br.bitOff < 8` — needed for bitstream correspondence (same as
   `readBit_toBits`). Without this, `toBits` drops `pos * 8 + bitOff`
   where `bitOff ≥ 8` would put us in the wrong byte.

2. `hn : n ≤ 32` — needed because native `readBits.go` uses
   `bit <<< shift.toUInt32` where `UInt32.shiftLeft` reduces shift
   mod 32. For shift ≥ 32, the bit is placed at the wrong position.
   (In practice all callers use n ≤ 25, matching the docstring.)

#### Minor: Duplicated `byteToBits_length`

`byteToBits_length'` in InflateCorrect.lean is identical to the private
`byteToBits_length` in Deflate.lean. Make the Deflate version non-private
and reuse it.

#### Minor: `ofFn_drop_head` can use stdlib

Replace the inductive proof with `List.drop_eq_getElem_cons` +
`List.getElem_ofFn`.

#### Observation: General-purpose lemmas

Several private helpers in InflateCorrect.lean are general-purpose and
could move to ZipForStd in a future session:
- `flatMap_drop_mul`: drop segments from flatMap with uniform-length outputs
- `shift_and_one_eq_testBit`: `(n >>> i) &&& 1 = if testBit then ...`
- `list_drop_cons_tail`: structural lemma about drop/cons
